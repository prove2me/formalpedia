-- Prove2me | solution 1 for Psi.psiPath_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:44:06.489278+00:00
-- url     : https://prove2.me/submissions/bdd561ea-26c8-4260-bd0d-109330f31b21

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_cUD_step
import Theorems.Thm_Psi_firstDDidx_repl_true_DD
import Theorems.Thm_Psi_firstDDidx_prepend
import Theorems.Thm_Psi_takeWhile_repl_true
import Theorems.Thm_Psi_takeWhile_repl_false
import Theorems.Thm_Psi_takeWhile_id_head_ne
import Theorems.Thm_Psi_takeWhile_false_head_ne

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (ρ ρ' : List Bool)
    (hb : 1 ≤ b)
    (hρU : ρ = [] ∨ ρ.head? = some true)
    (hρDD : hasDD ρ = false)
    (hmax : ρ.getLast? ≠ some true ∨ ρ'.head? ≠ some false)
    (hne : ρ ++ ρ' ≠ []) :
    psiPath ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
              ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
      = (List.replicate a false ++ List.replicate b true ++ [false] ++ (psiPath (ρ ++ ρ')).1,
         numN ρ :: (psiPath (ρ ++ ρ')).2) := by
  have hcUD : cUD ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
              ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') = a :=
    cUD_step a b ρ ρ' hb hρU
  set L := ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ' with hLdef
  have hLsplit1 : L = (ρ ++ List.replicate b true) ++ (List.replicate (b + 1) false ++ ρ') := by
    rw [hLdef]; simp [List.append_assoc]
  have hLsplit2 : L = ρ ++ (List.replicate b true ++ List.replicate (b + 1) false ++ ρ') := by
    rw [hLdef]; simp [List.append_assoc]
  have hLsplit3 : L = (ρ ++ List.replicate b true ++ List.replicate (b + 1) false) ++ ρ' := by
    rw [hLdef]
  have hrestL : List.drop (2 * a + 1)
      ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') = L := by
    have hPeq : (List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
        = ((List.replicate a [true, false]).flatten ++ [true]) ++ L := by
      rw [hLdef]; simp [List.append_assoc]
    rw [hPeq, show 2 * a + 1 = ((List.replicate a [true, false]).flatten ++ [true]).length from by
      simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega, List.drop_left]
  have ht_head : (List.replicate b true ++ List.replicate (b + 1) false ++ ρ').head? = some true := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [List.replicate_succ]; simp
  have ht_fdd : firstDDidx (List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
      = some b := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hEE : List.replicate (b' + 1 + 1) false ++ ρ'
        = false :: false :: (List.replicate b' false ++ ρ') := by
      rw [show b' + 1 + 1 = b' + 2 from rfl, List.replicate_succ, List.replicate_succ]; rfl
    rw [List.append_assoc, hEE, firstDDidx_repl_true_DD]
  have hfdd : firstDDidx L = some (ρ.length + b) := by
    rw [hLsplit2]; exact firstDDidx_prepend ρ _ b hρDD ht_head ht_fdd
  have htake_i0 : L.take (ρ.length + b) = ρ ++ List.replicate b true := by
    rw [hLsplit1, show ρ.length + b = (ρ ++ List.replicate b true).length from by simp,
      List.take_left]
  have hdrop_i0 : L.drop (ρ.length + b) = List.replicate (b + 1) false ++ ρ' := by
    rw [hLsplit1, show ρ.length + b = (ρ ++ List.replicate b true).length from by simp,
      List.drop_left]
  have hρrec : L.take (ρ.length + b - b) = ρ := by
    rw [show ρ.length + b - b = ρ.length from by omega, hLsplit2, List.take_left]
  have hρ'rec : L.drop (ρ.length + b + b + 1) = ρ' := by
    rw [hLsplit3, show ρ.length + b + b + 1
      = (ρ ++ List.replicate b true ++ List.replicate (b + 1) false).length from by
        simp [List.append_assoc]; omega, List.drop_left]
  have hbc : min ((L.take (ρ.length + b)).reverse.takeWhile id).length
                 (((L.drop (ρ.length + b)).takeWhile (· = false)).length - 1) = b := by
    rw [htake_i0, hdrop_i0, List.reverse_append, List.reverse_replicate, takeWhile_repl_true,
        takeWhile_repl_false]
    simp only [List.length_append, List.length_replicate]
    rcases hmax with hm | hm
    · have : (ρ.reverse.takeWhile id).length = 0 :=
        takeWhile_id_head_ne _ (by rw [List.head?_reverse]; exact hm)
      omega
    · have : (ρ'.takeWhile (· = false)).length = 0 := takeWhile_false_head_ne _ hm
      omega
  rw [psiPath.eq_1, hcUD, hrestL]
  split
  · next h => rw [hfdd] at h; exact absurd h (by simp)
  · next i h =>
      rw [hfdd] at h; injection h with hh; subst hh
      simp only [hbc, hρrec, hρ'rec]
      rw [dif_neg hne]
end Psi
