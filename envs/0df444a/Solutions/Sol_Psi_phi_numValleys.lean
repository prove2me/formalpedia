-- Prove2me | solution 1 for Psi.phi_numValleys
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:34:15.003545+00:00
-- url     : https://prove2.me/submissions/692e4b4a-f81b-4e96-8742-55f4f1948f23

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_phi_isDyck
import Theorems.Thm_Psi_dyck_head
import Theorems.Thm_Psi_dyck_stEast
import Theorems.Thm_Psi_filterF_replicate_false
import Theorems.Thm_Psi_filterF_replicate_true
import Theorems.Thm_Psi_noDescent_false_decomp
import Theorems.Thm_Psi_numValleys_base
import Theorems.Thm_Psi_numValleys_construction
import Theorems.Thm_Psi_phiPath_ne_nil
import Theorems.Thm_Psi_sar_bound_pos
import Theorems.Thm_Psi_splitAtRow_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) :
    numValleys (phiPath w av) = (w.filter (· = false)).length := by
  fun_induction phiPath w av with
  | case1 w av hnd => exact numValleys_base _ _
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      have hnd' : noDescent w = false := by simpa using hnd
      have hdec : w = List.replicate a false ++ List.replicate b true ++ false :: w' :=
        (noDescent_false_decomp hnd').1
      have hb1 : 1 ≤ b := (noDescent_false_decomp hnd').2
      have hpiD : IsDyck pi := phi_isDyck w' av'
      have hpine : pi ≠ [] := phiPath_ne_nil w' av'
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
      rw [show (List.replicate a [true, false]).flatten ++ [true] ++ rho ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho' = fUD a ++ [true] ++ rho ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho' from rfl]
      rw [numValleys_construction a b rho rho' hb1 hbd, happ, ihrec]
      conv_rhs => rw [hdec]
      simp only [List.filter_append, List.length_append, filterF_replicate_false,
        filterF_replicate_true, List.filter_cons, decide_true, if_true, List.length_cons]
      omega
end Psi
