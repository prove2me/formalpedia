-- Prove2me | solution 1 for Psi.psi_rest_struct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:47:46.942815+00:00
-- url     : https://prove2.me/submissions/8cecaba6-8f94-4e76-9c05-018e87ca6dc8

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_head_dropWhile_false
import Theorems.Thm_Psi_lead_false_split
import Theorems.Thm_Psi_trail_true_split
import Theorems.Thm_Psi_firstDDidx_lt
import Theorems.Thm_Psi_firstDDidx_drop_ff
import Theorems.Thm_Psi_firstDDidx_take_noDD
import Theorems.Thm_Psi_firstDDidx_prev_true
import Theorems.Thm_Psi_hasDD_prefix
import Theorems.Thm_Psi_numN_cons_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rest : List Bool) (i p L b : ℕ)
    (h : firstDDidx rest = some i) (hstart : rest.head? = some true)
    (hp : p = ((rest.take i).reverse.takeWhile id).length)
    (hL : L = ((rest.drop i).takeWhile (· = false)).length)
    (hb : b = min p (L - 1)) :
    rest = rest.take (i - b) ++ List.replicate b true ++ List.replicate (b + 1) false
             ++ rest.drop (i + b + 1)
      ∧ hasDD (rest.take (i - b)) = false
      ∧ ((rest.take (i - b)).getLast? ≠ some true ∨ (rest.drop (i + b + 1)).head? ≠ some false)
      ∧ 1 ≤ b
      ∧ (numN (rest.take (i - b)) = 0 → rest.take (i - b) = []) := by
  have hiLt : i + 1 < rest.length := firstDDidx_lt rest i h
  have hAlen : (rest.take i).length = i := by rw [List.length_take]; omega
  obtain ⟨htrailA, hgl⟩ := trail_true_split (rest.take i)
  rw [hAlen, ← hp] at htrailA hgl
  have hAtake : (rest.take i).take (i - p) = rest.take (i - p) := by rw [List.take_take]; congr 1; omega
  rw [hAtake] at htrailA hgl
  have hleadB := lead_false_split (rest.drop i)
  rw [← hL] at hleadB
  set B1 := (rest.drop i).dropWhile (· = false) with hB1
  have hB1head : B1.head? ≠ some false := head_dropWhile_false _
  have hL2 : 2 ≤ L := by
    obtain ⟨r, hr⟩ := firstDDidx_drop_ff rest i h
    rw [hL, hr]; simp [List.takeWhile]
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exfalso; obtain ⟨r, hr⟩ := firstDDidx_drop_ff rest i h
      rw [h0, List.drop_zero] at hr; rw [hr] at hstart; simp at hstart
    · exact hpos
  have hpi : p ≤ i := by
    rw [hp]
    have := (List.takeWhile_sublist (l := (rest.take i).reverse) id).length_le
    rw [List.length_reverse, hAlen] at this; exact this
  have hp1 : 1 ≤ p := by
    have hgt : (rest.take i).getLast? = some true := firstDDidx_prev_true rest i h hi1
    have hrh : (rest.take i).reverse.head? = some true := by rw [List.head?_reverse]; exact hgt
    obtain ⟨t, ht⟩ : ∃ t, (rest.take i).reverse = true :: t := by
      cases hc : (rest.take i).reverse with
      | nil => rw [hc] at hrh; simp at hrh
      | cons x xs => rw [hc] at hrh; simp only [List.head?_cons, Option.some.injEq] at hrh
                     subst hrh; exact ⟨xs, rfl⟩
    rw [hp, ht]; simp [List.takeWhile]
  have hb1 : 1 ≤ b := by rw [hb]; omega
  have hlenip : (rest.take (i - p)).length = i - p := by rw [List.length_take]; omega
  have hG1 : rest.take (i - b) = rest.take (i - p) ++ List.replicate (p - b) true := by
    have ht : rest.take (i - b) = (rest.take i).take (i - b) := by rw [List.take_take]; congr 1; omega
    rw [ht, htrailA, List.take_append, hlenip, show i - b - (i - p) = p - b from by omega,
      List.take_of_length_le (by rw [hlenip]; omega), List.take_replicate, Nat.min_eq_left (by omega)]
  have hG2 : rest.drop (i + b + 1) = List.replicate (L - b - 1) false ++ B1 := by
    have hdd : rest.drop (i + b + 1) = (rest.drop i).drop (b + 1) := by rw [List.drop_drop]; congr 1
    rw [hdd, hleadB, List.drop_append_of_le_length (by rw [List.length_replicate]; omega),
      List.drop_replicate]
    exact congrArg (fun n => List.replicate n false ++ B1) (by omega)
  refine ⟨?_, ?_, ?_, hb1, ?_⟩
  · conv_lhs => rw [← List.take_append_drop i rest, htrailA, hleadB]
    rw [hG1, hG2,
      show List.replicate p true = List.replicate (p - b) true ++ List.replicate b true from by
        rw [← List.replicate_add]; congr 1; omega,
      show List.replicate L false = List.replicate (b + 1) false ++ List.replicate (L - b - 1) false from by
        rw [← List.replicate_add]; congr 1; omega]
    simp only [List.append_assoc]
  · have hnoA : hasDD (rest.take i) = false := firstDDidx_take_noDD rest i h
    have hpre : rest.take i = rest.take (i - b) ++ (rest.take i).drop (i - b) := by
      rw [show rest.take (i - b) = (rest.take i).take (i - b) from by rw [List.take_take]; congr 1; omega,
        List.take_append_drop]
    rw [hpre] at hnoA
    exact hasDD_prefix _ _ hnoA
  · rcases (by omega : b = p ∨ b = L - 1) with hbp | hbL
    · left; rw [hG1, show p - b = 0 from by omega]; simpa using hgl
    · right; rw [hG2, show L - b - 1 = 0 from by omega]; simpa using hB1head
  · intro h0
    by_contra hc
    have hib : 0 < i - b := by
      have := List.length_pos_of_ne_nil hc; rw [List.length_take] at this; omega
    have hh : (rest.take (i - b)).head? = rest.head? := by rw [List.head?_take, if_neg (by omega)]
    obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hc
    rw [hys] at hh; simp only [List.head?_cons] at hh
    rw [hstart] at hh
    have hy : y = true := Option.some.inj hh
    subst hy; rw [hys, numN_cons_true] at h0; omega
end Psi
