-- Prove2me | solution 1 for Psi.psi_phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:46:13.578819+00:00
-- url     : https://prove2.me/submissions/82fa2770-f92d-436e-9ce1-4f2ba333da4e

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_splitAtRow_fst_head
import Theorems.Thm_Psi_splitAtRow_max
import Theorems.Thm_Psi_noDescent_true_eq
import Theorems.Thm_Psi_psiPath_base
import Theorems.Thm_Psi_psiPath_step
import Theorems.Thm_Psi_desComp_noDescent
import Theorems.Thm_Psi_dyck_head
import Theorems.Thm_Psi_isValid_av_cons
import Theorems.Thm_Psi_isValid_head_le
import Theorems.Thm_Psi_isValid_tail
import Theorems.Thm_Psi_noDescent_false_decomp
import Theorems.Thm_Psi_phiPath_ne_nil
import Theorems.Thm_Psi_phi_isDyck
import Theorems.Thm_Psi_phi_split_noDD
import Theorems.Thm_Psi_splitAtRow_append
import Theorems.Thm_Psi_split_numN
import Theorems.Thm_Psi_tau_headD_le_numN


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) (h : IsValid w av) :
    psiPath (phiPath w av) = (w, av) := by
  revert h
  fun_induction phiPath w av with
  | case1 w av hnd =>
      intro hv
      have hnd' : noDescent w = true := by simpa using hnd
      set l := (w.filter (· = false)).length with hl
      set k := (w.filter id).length with hk
      have hlen : av.length = 1 := by
        have := hv.1; rw [desComp_noDescent hnd'] at this; simpa using this
      obtain ⟨a0, rfl⟩ : ∃ a0, av = [a0] := by
        cases av with
        | nil => simp at hlen
        | cons x xs => cases xs with
          | nil => exact ⟨x, rfl⟩
          | cons _ _ => simp at hlen
      have ha0 : a0 = 0 := by
        have := hv.2.2
        rw [tauOf, desComp_noDescent hnd'] at this
        simp only [deltaOf, deltaAux, zero_add, List.zipWith_cons_cons, List.zipWith_nil_right,
          List.getLast?_singleton, Option.some.injEq] at this
        omega
      subst ha0
      rw [psiPath_base l k]
      have hw : w = List.replicate l false ++ List.replicate k true := noDescent_true_eq w hnd'
      rw [← hw]
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      intro hv
      have hnd' : noDescent w = false := by simpa using hnd
      have ivt : IsValid w' av' := isValid_tail w av hv hnd'
      have hb : 1 ≤ b := (noDescent_false_decomp hnd').2
      have hpiD : IsDyck pi := phi_isDyck w' av'
      have hpine : pi ≠ [] := phiPath_ne_nil w' av'
      have happ : rho ++ rho' = pi := by
        have := splitAtRow_append pi hh; rw [hsplit] at this; simpa using this
      have hle := isValid_head_le w av hv hnd'
      have hnoDD : hasDD rho = false := by
        have := phi_split_noDD w' av' ivt hh hle
        rw [hsplit] at this; simpa using this
      have hbound : hh ≤ numN pi := le_trans hle (tau_headD_le_numN w' av' ivt)
      have hnumN : numN rho = hh := by
        have := split_numN pi hh hbound; rw [hsplit] at this; simpa using this
      have hpihead : pi.head? = some true := dyck_head pi hpiD hpine
      have hρU : rho = [] ∨ rho.head? = some true := by
        rcases splitAtRow_fst_head pi hh with h | h
        · left; rw [hsplit] at h; simpa using h
        · right; rw [hsplit] at h; simp only at h; rw [h, hpihead]
      have hmax : rho.getLast? ≠ some true ∨ rho'.head? ≠ some false := by
        rcases splitAtRow_max pi hh with h | h
        · left; rw [hsplit] at h; simpa using h
        · right; rw [hsplit] at h; simpa using h
      have hne : rho ++ rho' ≠ [] := by rw [happ]; exact hpine
      rw [psiPath_step a b rho rho' hb hρU hnoDD hmax hne, happ, ihrec ivt, hnumN]
      have hav : av = hh :: av' := isValid_av_cons w av hv hnd'
      refine Prod.ext ?_ ?_
      · show List.replicate a false ++ List.replicate b true ++ [false] ++ w' = w
        conv_rhs => rw [(noDescent_false_decomp hnd').1]
        simp only [List.append_assoc, List.singleton_append]
        rfl
      · show hh :: av' = av
        rw [hav]
end Psi
