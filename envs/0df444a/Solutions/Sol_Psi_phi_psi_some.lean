-- Prove2me | solution 1 for Psi.phi_psi_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:52:54.524125+00:00
-- url     : https://prove2.me/submissions/5c5529cf-fea4-4f11-ba39-536fa11f73ef

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_psi_rest_struct
import Theorems.Thm_Psi_fUD_len
import Theorems.Thm_Psi_dyck_leading
import Theorems.Thm_Psi_dyck_rest_head
import Theorems.Thm_Psi_dyck_residual
import Theorems.Thm_Psi_phiPath_block
import Theorems.Thm_Psi_noDescent_sorted
import Theorems.Thm_Psi_psiPath_base
import Theorems.Thm_Psi_psiPath_step
import Theorems.Thm_Psi_splitAtRow_reconstruct


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ)
    (IH : ∀ m, m < n → ∀ π : List Bool, π.length = m → IsDyck π → π ≠ [] →
      phiPath (psiPath π).1 (psiPath π).2 = π)
    (π : List Bool) (hlen : π.length = n) (hd : IsDyck π) (hne : π ≠ []) (i : ℕ)
    (hfd : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    phiPath (psiPath π).1 (psiPath π).2 = π := by
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
    rw [hpsi, hbase, phiPath.eq_1, if_pos (by simpa using noDescent_sorted a b)]
    simp [List.filter_append, List.append_assoc]
  · have hpsi : psiPath π = (List.replicate a false ++ List.replicate b true ++ [false]
          ++ (psiPath (ρ ++ ρ')).1, numN ρ :: (psiPath (ρ ++ ρ')).2) := by
      rw [hπ]; exact psiPath_step a b ρ ρ' hb1 hρU hρDD hmax hemp
    rw [hpsi]
    have hreslen : (ρ ++ ρ').length < n := by
      rw [← hlen]; conv_rhs => rw [hπ]
      simp only [List.length_append, List.length_cons, List.length_replicate, fUD_len,
        List.length_nil]; omega
    have hIH := IH (ρ ++ ρ').length hreslen (ρ ++ ρ') rfl hresD hemp
    rw [phiPath_block a b (psiPath (ρ ++ ρ')).1 (numN ρ) (psiPath (ρ ++ ρ')).2 hb1, hIH,
      splitAtRow_reconstruct ρ ρ' hne0 hρDD hmax]
    exact hπ.symm
end Psi
