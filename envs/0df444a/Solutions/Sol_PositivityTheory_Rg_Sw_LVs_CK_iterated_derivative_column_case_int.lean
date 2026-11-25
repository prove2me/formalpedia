-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.iterated_derivative_column_case_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:27.80614+00:00
-- url     : https://prove2.me/submissions/26554e99-f9b3-418d-9d5e-bafb87ca75a9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivFsum
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedDerivativeColumnCaseInt
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_determinant_power_zero_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_fderiv_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_fsum
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_ev_piF
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_determinant_power_column_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_fsum
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_icompL
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_iconst_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_ipeel
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiF_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiF_single
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiF_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiF_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piF_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piF_single_succ
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piF_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piF_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.phiL_apply
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.piL_apply



set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (t : ℤ) (M : ℕ) (e : Equiv.Perm (Fin (M + 1))) (c : Fin (M + 1)) :
    iteratedFDeriv ℂ (M + 1) (fun y => fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1) =
      -iteratedFDeriv ℂ (M + 1) (H (M + 1) t) 0 (fun k => Matrix.single k (e k) 1) := by
  have hσ : ∀ k : Fin (M + 1), Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ =
      Equiv.swap 0 c.succ (e k).succ :=
    fun k => Equiv.Perm.decomposeFin_symm_apply_succ e c.succ k
  have hG : AnalyticAt ℂ (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)
  have e1 := icompL (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) phiF phiF_add phiF_smul 0 0
    phiF_zero hG (M + 1)
    (fun k => Matrix.single k (Equiv.swap 0 c.succ (e k).succ) 1)
    (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1)
    (fun i => by rw [phiF_single, hσ])
  rw [← e1]
  have hev : (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) ∘ phiF =ᶠ[𝓝 0] fsum t c := by
    filter_upwards [ev_piF (M + 1)] with X hX
    exact fderiv_determinant_power_column_sum t X hX c
  rw [(hev.iteratedFDeriv ℂ (M + 1)).eq_of_nhds]
  have h0 : (1 + piF (0 : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) ℂ)).det ≠ 0 := by
    simp [piF_zero]
  rw [ipeel (fsum t c) 0 (analyticAt_fsum t c 0 h0) M _ (e.symm c)]
  beta_reduce
  have hu0 : Equiv.swap 0 c.succ (e (e.symm c)).succ = 0 := by simp
  rw [hu0]
  have hev2 : (fun y => fderiv ℂ (fsum t c) y (Matrix.single (e.symm c) 0 1)) =ᶠ[𝓝 0]
      (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
        (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) ∘ piF := by
    filter_upwards [ev_piF (M + 1)] with y hy
    simp [fderiv_fsum t c (e.symm c) y hy]
  erw [(hev2.iteratedFDeriv ℂ M).eq_of_nhds]
  have hK : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)
  have hK' : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0 :=
    analyticAt_const.mul hK
  have hne : ∀ k : Fin M, Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ =
      (e ((e.symm c).succAbove k)).succ := by
    intro k
    have h1 : e ((e.symm c).succAbove k) ≠ c := by
      intro h
      have h2 := congrArg e.symm h
      rw [Equiv.symm_apply_apply] at h2
      exact Fin.succAbove_ne _ _ h2
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => h1 (Fin.succ_injective _ h))
  erw [icompL (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1))
    piF piF_add piF_smul 0 0 piF_zero hK' M
    (fun k => Matrix.single ((e.symm c).succAbove k)
      (Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ) 1)
    (fun k => Matrix.single ((e.symm c).succAbove k) (e ((e.symm c).succAbove k)) 1)
    (fun k => by rw [hne, piF_single_succ])]
  rw [iconst_mul _ 0 (-1) hK]
  rw [ipeel (H (M + 1) t) 0 (analyticAt_determinant_power_zero_int _ t) M (fun k => Matrix.single k (e k) 1) (e.symm c)]
  clear e1 hev hev2 hK' hne hσ hG h0 hu0 hK
  simp
  rfl
end PositivityTheory.Rg.Sw.LVs.CK
