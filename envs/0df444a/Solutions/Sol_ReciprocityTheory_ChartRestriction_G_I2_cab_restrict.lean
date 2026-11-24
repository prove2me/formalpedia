-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:36.756052+00:00
-- url     : https://prove2.me/submissions/cf8278fe-0d5d-4226-a445-1abbb292fb83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (Sb : Submodule ℂ V)
    {c : ℕ} {f g : V → ℂ} (hf : ContDiff ℂ c f) (hg : ContDiff ℂ c g) (hfg : ∀ v ∈ Sb, f v = g v)
    (x : Fin c → V) (hx : ∀ k, x k ∈ Sb) :
    iteratedFDeriv ℂ c f 0 x = iteratedFDeriv ℂ c g 0 x := by
  let ι : Sb →L[ℂ] V := Sb.subtypeL
  have hfi : f ∘ ι = g ∘ ι := by funext v; exact hfg v v.2
  have e1 := ι.iteratedFDeriv_comp_right hf (0 : Sb) le_rfl
  have e2 := ι.iteratedFDeriv_comp_right hg (0 : Sb) le_rfl
  rw [hfi, e2] at e1
  have := congrArg (fun M => M (fun k => (⟨x k, hx k⟩ : Sb))) e1
  simpa [ι, ContinuousMultilinearMap.compContinuousLinearMap_apply] using this.symm
end ReciprocityTheory.ChartRestriction.G.I2
