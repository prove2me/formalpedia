-- Prove2me | solution 1 for Psi.phi_riseComp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:52:03.643779+00:00
-- url     : https://prove2.me/submissions/0cdce44b-96ee-4606-9ca6-0d8899b6910b

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_muVecAux_head_shift
import Theorems.Thm_Psi_tauOf_head_pos
import Theorems.Thm_Psi_muVec_tauOf_descent
import Theorems.Thm_Psi_cc_append_replicate_true
import Theorems.Thm_Psi_cc_replicate_false
import Theorems.Thm_Psi_cc_fUD_cons_true
import Theorems.Thm_Psi_northRuns_replicate_true_replicate_false
import Theorems.Thm_Psi_riseComp_split
import Theorems.Thm_Psi_muVec_headD
import Theorems.Thm_Psi_riseComp_recon
import Theorems.Thm_Psi_desComp_noDescent
import Theorems.Thm_Psi_isValid_av_cons
import Theorems.Thm_Psi_isValid_head_le
import Theorems.Thm_Psi_isValid_tail
import Theorems.Thm_Psi_len_filter_split
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
    northRuns (cc (phiPath w av)) = muVec (tauOf w av) := by
  revert h
  fun_induction phiPath w av with
  | case1 w av hnd =>
      intro hv
      have hnd' : noDescent w = true := by simpa using hnd
      -- base path `= fUD l ++ true :: (replicate k true ++ replicate (k+1) false)`
      set l := (w.filter (· = false)).length with hl
      set k := (w.filter id).length with hk
      have hlk : l + k = w.length := by rw [hl, hk]; exact len_filter_split w
      have hpath : (List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
            ++ List.replicate (k + 1) false
          = fUD l ++ true :: (List.replicate k true ++ List.replicate (k + 1) false) := by
        rw [fUD, List.replicate_succ]; simp [List.append_assoc]
      rw [hpath, cc_fUD_cons_true, cc_append_replicate_true, cc_replicate_false,
        ← List.append_assoc, ← List.replicate_add]
      rw [northRuns_replicate_true_replicate_false _ _ (by omega)]
      -- muVec side
      rw [tauOf, desComp_noDescent hnd']
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
      simp only [deltaOf, deltaAux, zero_add, List.zipWith_cons_cons, List.zipWith_nil_right,
        add_zero, muVec, muVecAux, List.append_nil]
      have : 0 < w.length + 1 := by omega
      rw [if_pos (by omega)]
      congr 1
      omega
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
      rw [riseComp_recon a b hh rho rho' hb hnoDD hnumN]
      -- algebra of τ
      have hL : 0 < (tauOf w' av').headD 0 := tauOf_head_pos w' av' ivt
      have hIH : northRuns (cc pi) = muVec (tauOf w' av') := ihrec ivt
      have hav : av = hh :: av' := isValid_av_cons w av hv hnd'
      have hmu : muVec (tauOf w av) = (a + 1 + b + hh) :: muVecAux (tauOf w' av') hh := by
        rw [hav]; exact muVec_tauOf_descent hnd' hh av'
      rw [hmu]
      -- match the two `cons`es
      refine congrArg (List.cons _) ?_
      -- tail: `northRuns (cc rho') = muVecAux (tauOf w' av') hh`
      rw [muVecAux_head_shift (tauOf w' av') hh hL]
      have hsplitG := riseComp_split rho rho' hnoDD
      rw [happ, hIH, muVec_headD (tauOf w' av') hL, hnumN] at hsplitG
      rw [hsplitG]
end Psi
