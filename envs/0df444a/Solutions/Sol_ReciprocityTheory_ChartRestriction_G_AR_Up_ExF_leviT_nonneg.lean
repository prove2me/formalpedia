-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.leviT_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:39.172928+00:00
-- url     : https://prove2.me/submissions/4a14a3cc-04f3-4e77-bac5-97f266d38cf0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_sqNorm_nonneg__56844cb7c596
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhD_cd_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_two_le_infty
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviLogNormSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution {n : ℕ} (v0 : V n) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ)) v0 ξ).re := by
  let g : Fin (n + 1) → V n → ℂ := fun i =>
    Fin.cons (α := fun _ => V n → ℂ) (fun _ : V n => (1 : ℂ)) (fun j : Fin n => fun y : V n => y j) i
  have hc : ∀ i, ContDiffAt ℂ 2 (g i) v0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [g, Fin.cons_zero]; exact contDiffAt_const
    · simp only [g, Fin.cons_succ]; exact (cd_coord _).contDiffAt.of_le two_le_infty
  have hne : (fun i => g i v0) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [g] at this
  have h := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n (n + 1) g v0 ξ hc hne
  have e1 : (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ) := by
    funext y
    simp [sqNorm, Fin.sum_univ_succ, g, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
  rw [e1] at h
  rw [h, Complex.ofReal_re]
  exact div_nonneg (sqNorm_nonneg' _) (sqNorm_nonneg' _)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
