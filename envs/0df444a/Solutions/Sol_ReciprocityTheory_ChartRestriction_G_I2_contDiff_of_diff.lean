-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:45:54.607013+00:00
-- url     : https://prove2.me/submissions/94e511de-84f0-43c3-993d-84f53eed7423

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_differentiable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {f : W → ℂ} (hf : Differentiable ℂ f) : ContDiff ℂ (⊤ : ℕ∞) f := by
  let e := (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (f ∘ e.symm) := by
    first
    | exact hf.comp e.symm.differentiable
    | exact hf.comp (e.symm.contDiff.differentiable (by simp))
  have h3 := (contDiff_of_differentiable h1 (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp e.contDiff
  convert h3 using 1
  funext v; simp
end ReciprocityTheory.ChartRestriction.G.I2
