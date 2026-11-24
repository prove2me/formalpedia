-- Prove2me | solution 1 for Psi.psi_valid_head_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:53:42.728849+00:00
-- url     : https://prove2.me/submissions/d8b4a16d-bf17-4194-a485-fcbad399501d

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_numN_le_numNBeforeDD_append
import Theorems.Thm_Psi_numNBeforeDD_base_step
import Theorems.Thm_Psi_numNBeforeDD_reconstruct
import Theorems.Thm_Psi_isValid_zeros_ones
import Theorems.Thm_Psi_isValid_cons
import Theorems.Thm_Psi_cLead0_block
import Theorems.Thm_Psi_cLead1_block
import Theorems.Thm_Psi_desComp_noDescent
import Theorems.Thm_Psi_drop_a_block
import Theorems.Thm_Psi_dyck_leading
import Theorems.Thm_Psi_dyck_residual
import Theorems.Thm_Psi_dyck_rest_head
import Theorems.Thm_Psi_fUD_len
import Theorems.Thm_Psi_noDescent_block
import Theorems.Thm_Psi_noDescent_sorted
import Theorems.Thm_Psi_psiPath_base
import Theorems.Thm_Psi_psiPath_step
import Theorems.Thm_Psi_psi_rest_struct
import Theorems.Thm_Psi_tauOf_descent


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ)
    (IH : ∀ m, m < n → ∀ π : List Bool, π.length = m → IsDyck π → π ≠ [] →
      IsValid (psiPath π).1 (psiPath π).2 ∧
        (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π)
    (π : List Bool) (hlen : π.length = n) (hd : IsDyck π) (hne : π ≠ []) (i : ℕ)
    (hfd : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    IsValid (psiPath π).1 (psiPath π).2 ∧
      (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π := by
  set a := cUD π with hadef
  set rest := π.drop (2 * a + 1) with hrestdef
  have hstart : rest.head? = some true := dyck_rest_head π i hd hne hfd
  set p := ((rest.take i).reverse.takeWhile id).length with hpdef
  set L := ((rest.drop i).takeWhile (· = false)).length with hLdef
  set b := min p (L - 1) with hbdef
  set ρ := rest.take (i - b) with hρdef
  set ρ' := rest.drop (i + b + 1) with hρ'def
  obtain ⟨hstruct, hρDD, hmax, hb1, hne0⟩ :=
    psi_rest_struct rest i p L b hfd hstart hpdef hLdef hbdef
  simp only [← hρdef, ← hρ'def] at hstruct hρDD hmax hne0
  have hπ : π = (List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ' := by
    have hl := dyck_leading π hd hne
    rw [← hadef, ← hrestdef, hstruct] at hl
    rw [hl]; simp [List.append_assoc]
  have hρU : ρ = [] ∨ ρ.head? = some true := by
    rcases Nat.eq_zero_or_pos (numN ρ) with h0 | hpos
    · left; exact hne0 h0
    · right
      have hlt : 0 < ρ.length := by
        by_contra hc; push_neg at hc
        rw [Nat.le_zero, List.length_eq_zero_iff] at hc; rw [hc] at hpos; simp [numN] at hpos
      have hh : ρ.head? = rest.head? := by
        rw [hρdef, List.head?_take, if_neg (by intro hz; rw [hρdef, hz] at hlt; simp at hlt)]
      rw [hh, hstart]
  have hresD : IsDyck (ρ ++ ρ') := dyck_residual π b ρ ρ' hd hne hstruct hρDD hρU
  by_cases hemp : ρ ++ ρ' = []
  · obtain ⟨hρe, hρ'e⟩ := List.append_eq_nil_iff.mp hemp
    have hbase : π = (List.replicate a [true, false]).flatten
        ++ List.replicate (b + 1) true ++ List.replicate (b + 1) false := by
      rw [hπ, hρe, hρ'e]; simp [List.replicate_succ, List.append_assoc]
    have hpsi : psiPath π = (List.replicate a false ++ List.replicate b true, [0]) := by
      rw [hbase]; exact psiPath_base a b
    refine ⟨?_, ?_⟩
    · rw [hpsi]; exact isValid_zeros_ones a b
    · have h1 : (psiPath π).1 = List.replicate a false ++ List.replicate b true := by rw [hpsi]
      have h2 : (psiPath π).2 = [0] := by rw [hpsi]
      rw [h1, h2]
      have hrhs : numNBeforeDD π = a + b + 1 := by rw [hbase, numNBeforeDD_base_step]
      rw [hrhs]
      have hnd : noDescent (List.replicate a false ++ List.replicate b true) = true :=
        noDescent_sorted a b
      rw [tauOf, desComp_noDescent hnd]
      simp only [deltaOf, deltaAux, zero_add, List.zipWith_cons_cons, List.zipWith_nil_left,
        List.headD_cons, add_zero, List.length_append, List.length_replicate]
  · have hpsi : psiPath π = (List.replicate a false ++ List.replicate b true ++ [false]
          ++ (psiPath (ρ ++ ρ')).1, numN ρ :: (psiPath (ρ ++ ρ')).2) := by
      rw [hπ]; exact psiPath_step a b ρ ρ' hb1 hρU hρDD hmax hemp
    have hreslen : (ρ ++ ρ').length < n := by
      rw [← hlen]; conv_rhs => rw [hπ]
      simp only [List.length_append, List.length_cons, List.length_replicate, fUD_len,
        List.length_nil]; omega
    obtain ⟨hvalid', hhead'⟩ := IH (ρ ++ ρ').length hreslen (ρ ++ ρ') rfl hresD hemp
    set w' := (psiPath (ρ ++ ρ')).1 with hw'def
    set av' := (psiPath (ρ ++ ρ')).2 with hav'def
    have hbound : numN ρ ≤ (tauOf w' av').headD 0 := by
      rw [hhead']; exact numN_le_numNBeforeDD_append ρ ρ' hρDD
    refine ⟨?_, ?_⟩
    · rw [hpsi]
      exact isValid_cons a b w' av' hb1 hvalid' (numN ρ) hbound
    · have h1 : (psiPath π).1 = List.replicate a false ++ List.replicate b true ++ false :: w' := by
        rw [hpsi]; simp [List.append_assoc]
      have h2 : (psiPath π).2 = numN ρ :: av' := by rw [hpsi]
      have hrhs : numNBeforeDD π = a + 1 + numN ρ + b := by
        rw [hπ]; exact numNBeforeDD_reconstruct a b ρ ρ' hb1 hρDD
      rw [h1, h2, tauOf_descent (noDescent_block a b w' hb1), hrhs]
      simp only [List.headD_cons]
      rw [cLead0_block a b w' hb1, drop_a_block a b w', cLead1_block b w']
      omega
end Psi
