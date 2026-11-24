-- Prove2me | solution 1 for Psi.phi_split_noDD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:40:21.638636+00:00
-- url     : https://prove2.me/submissions/286d2385-bd74-4988-9ff2-a25553f590c2

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_split_numN
import Theorems.Thm_Psi_hasDD_append_false
import Theorems.Thm_Psi_hasDD_replicate_true
import Theorems.Thm_Psi_hasDD_fUD
import Theorems.Thm_Psi_hasDD_split_of_B
import Theorems.Thm_Psi_hasDD_split_base
import Theorems.Thm_Psi_tauOf_descent
import Theorems.Thm_Psi_isValid_tail
import Theorems.Thm_Psi_isValid_head_le
import Theorems.Thm_Psi_isValid_av_cons
import Theorems.Thm_Psi_tau_headD_le_numN
import Theorems.Thm_Psi_len_filter_split
import Theorems.Thm_Psi_noDescent_false_decomp
import Theorems.Thm_Psi_numN_append
import Theorems.Thm_Psi_numN_fUD
import Theorems.Thm_Psi_numN_phiPath
import Theorems.Thm_Psi_numN_replicate_true
import Theorems.Thm_Psi_numN_single_true
import Theorems.Thm_Psi_phi_isDyck
import Theorems.Thm_Psi_stEast_append
import Theorems.Thm_Psi_stEast_replicate_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w' : List Bool) (av' : List ℕ) (hv : IsValid w' av')
    (h : ℕ) (hle : h ≤ (tauOf w' av').headD 0) :
    hasDD (splitAtRow (phiPath w' av') h).1 = false := by
  revert hle; revert h; revert hv
  fun_induction phiPath w' av' with
  | case1 w' av' hnd =>
      intro hv h hle
      have hbound : h ≤ (w'.filter (· = false)).length + (w'.filter id).length + 1 := by
        have h1 := le_trans hle (tau_headD_le_numN w' av' hv)
        rw [numN_phiPath] at h1
        have h2 := len_filter_split w'
        omega
      exact hasDD_split_base _ _ h hbound
  | case2 w' av' hnd a after0 b w'' hh av'' pi rho rho' hsplit ihrec =>
      intro hv h hle
      have hnd' : noDescent w' = false := by simpa using hnd
      have ivt : IsValid w'' av'' := isValid_tail w' av' hv hnd'
      have hb1 : 1 ≤ b := (noDescent_false_decomp hnd').2
      have hpiD : IsDyck pi := phi_isDyck w'' av''
      have hhle : hh ≤ (tauOf w'' av'').headD 0 := isValid_head_le w' av' hv hnd'
      have hhnum : hh ≤ numN pi := le_trans hhle (tau_headD_le_numN w'' av'' ivt)
      have hrhoNoDD : hasDD rho = false := by
        have := ihrec ivt hh hhle; rw [hsplit] at this; simpa using this
      have hnumRho : numN rho = hh := by
        have := split_numN pi hh hhnum; rw [hsplit] at this; simpa using this
      have htau : (tauOf w' av').headD 0 = a + 1 + b + hh := by
        have hcons : av' = av'.headD 0 :: av'.tail := isValid_av_cons w' av' hv hnd'
        conv_lhs => rw [hcons, tauOf_descent hnd']
        rfl
      rw [show (List.replicate a [true, false]).flatten ++ [true] ++ rho ++ List.replicate b true
            ++ List.replicate (b + 1) false ++ rho'
          = ((List.replicate a [true, false]).flatten ++ [true] ++ rho ++ List.replicate b true
              ++ [false]) ++ (List.replicate b false ++ rho') from by
        rw [show List.replicate (b + 1) false = [false] ++ List.replicate b false from by
              rw [List.replicate_succ]; rfl]
        simp only [List.append_assoc]]
      apply hasDD_split_of_B
      · rw [stEast_append]; simp [stEast]
      · simp only [numN_append, numN_single_true, numN_replicate_true,
          show numN ((List.replicate a [true, false]).flatten) = a from numN_fUD a,
          show numN [false] = 0 from rfl, hnumRho]
        omega
      · apply hasDD_append_false
        · apply hasDD_append_false
          · apply hasDD_append_false
            · apply hasDD_append_false
              · exact hasDD_fUD a
              · rfl
              · intro _; simp
            · exact hrhoNoDD
            · intro hc; rw [stEast_append] at hc; simp [stEast] at hc
          · exact hasDD_replicate_true b
          · intro _; cases b <;> simp [List.replicate_succ]
        · rfl
        · intro hc
          rw [stEast_append, stEast_replicate_true] at hc
          simp [hb1] at hc
end Psi
