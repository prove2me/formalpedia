-- Prove2me | solution 1 for Psi.phi_area
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:52:03.011395+00:00
-- url     : https://prove2.me/submissions/bbde603a-5bad-4f3f-a6da-6b957c627254

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_split_numN
import Theorems.Thm_Psi_isValid_tail
import Theorems.Thm_Psi_isValid_head_le
import Theorems.Thm_Psi_isValid_av_cons
import Theorems.Thm_Psi_isValid_base_sum
import Theorems.Thm_Psi_tau_headD_le_numN
import Theorems.Thm_Psi_phi_split_noDD
import Theorems.Thm_Psi_area_base_zero
import Theorems.Thm_Psi_area_sandwich
import Theorems.Thm_Psi_dyck_head
import Theorems.Thm_Psi_dyck_stEast
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_noDescent_false_decomp
import Theorems.Thm_Psi_phiPath_ne_nil
import Theorems.Thm_Psi_phi_isDyck
import Theorems.Thm_Psi_sar_bound_pos
import Theorems.Thm_Psi_splitAtRow_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) (h : IsValid w av) :
    area (phiPath w av) = av.sum := by
  revert h
  fun_induction phiPath w av with
  | case1 w av hnd =>
      intro hv
      have hnd' : noDescent w = true := by simpa using hnd
      rw [isValid_base_sum w av hv hnd']
      exact area_base_zero _ _
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      intro hv
      have hnd' : noDescent w = false := by simpa using hnd
      have ivt : IsValid w' av' := isValid_tail w av hv hnd'
      have hb : 1 ≤ b := (noDescent_false_decomp hnd').2
      have hpiD : IsDyck pi := phi_isDyck w' av'
      have hpine : pi ≠ [] := phiPath_ne_nil w' av'
      have hpiV : validFrom pi 0 := ((isDyckAux_iff pi 0).mp hpiD).1
      have happ : rho ++ rho' = pi := by
        have := splitAtRow_append pi hh; rw [hsplit] at this; simpa using this
      have hbd : stEast rho false = false → rho'.head? = some true := by
        intro hsr
        by_cases hr0 : rho = []
        · have hpp : rho' = pi := by rw [hr0, List.nil_append] at happ; exact happ
          rw [hpp]; exact dyck_head pi hpiD hpine
        · have hfst : (splitAtRow pi hh).1 ≠ [] := by rw [hsplit]; exact hr0
          have hst : stEast (splitAtRow pi hh).1 false = false := by rw [hsplit]; exact hsr
          rcases sar_bound_pos pi hh hfst hst with h1 | h2
          · exfalso
            have hr'0 : rho' = [] := by rw [hsplit] at h1; exact h1
            have hrp : rho = pi := by rw [hr'0, List.append_nil] at happ; exact happ
            rw [hrp, dyck_stEast pi hpiD hpine] at hsr
            exact Bool.noConfusion hsr
          · rw [hsplit] at h2; exact h2
      have hle := isValid_head_le w av hv hnd'
      have hnoDD : hasDD rho = false := by
        have := phi_split_noDD w' av' ivt hh hle
        rw [hsplit] at this; simpa using this
      have hpiD' : IsDyck (rho ++ rho') := by rw [happ]; exact hpiD
      have hbound : hh ≤ numN pi := le_trans hle (tau_headD_le_numN w' av' ivt)
      have hnumN : numN rho = hh := by
        have := split_numN pi hh hbound; rw [hsplit] at this; simpa using this
      have hps : area pi = av'.sum := ihrec ivt
      rw [area_sandwich a b rho rho' hb hnoDD hbd hpiD', happ, hnumN, hps]
      have hcons : av = av.headD 0 :: av.tail := isValid_av_cons w av hv hnd'
      rw [hcons, List.sum_cons]
end Psi
