-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_entry_cd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:23.195645+00:00
-- url     : https://prove2.me/submissions/bf2357a2-62d3-4afd-bd71-01e1f7841e89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution (x0 : Frame X.Ψ r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => cpt X x0 z τ a b := by
  have hN : ∀ k : Fin r, ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ k b := by
    intro k
    by_cases h : b < k
    · simp only [nmat, dif_pos h]
      exact (show V (nd X) →L[ℂ] ℂ from EuclideanSpace.proj _).contDiff
    · simp only [nmat, dif_neg h]
      exact contDiff_const
  show ContDiff ℂ ∞ fun z : V (nd X) => (mat x0 τ * mat (nmat X z) τ) a b
  simp only [Matrix.mul_apply, mat, Matrix.of_apply]
  exact ContDiff.sum (fun k _ => contDiff_const.mul (hN k))
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
