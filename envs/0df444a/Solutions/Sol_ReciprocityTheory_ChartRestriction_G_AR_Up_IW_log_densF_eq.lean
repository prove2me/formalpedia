-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.log_densF_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:31.210282+00:00
-- url     : https://prove2.me/submissions/22818de3-6396-4ca1-92e3-fa5b622f8b63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_dmin_ne_zero

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
theorem _root_.solution (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Real.log (densF X x0 z) = ∑ τ, ∑ i : Fin r, (-2) * Lm X (cpt X x0 z) τ i.castSucc := by
  have hx : cpt X x0 z ∈ X.dom := hz
  have hd : ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := fun τ i => dmin_ne_zero X hx τ i
  unfold densF
  rw [Real.log_prod (fun τ _ => Finset.prod_ne_zero_iff.mpr
    (fun i _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hd τ _))))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Real.log_prod (fun i _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hd τ _)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.log_zpow]
  simp only [Lm]
  push_cast
  try ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
