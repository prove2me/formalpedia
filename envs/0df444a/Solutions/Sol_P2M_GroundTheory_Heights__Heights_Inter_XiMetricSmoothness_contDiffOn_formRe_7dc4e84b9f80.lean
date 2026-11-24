-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_formRe_7dc4e84b9f80
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:43.419355+00:00
-- url     : https://prove2.me/submissions/53b8977a-86fc-4a03-afcd-3078d7772aae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {n : WithTop ℕ∞}
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution {ι' : Type*} [Fintype ι'] {M : E → Matrix ι' ι' ℂ} {u v : E → ι' → ℂ}
    (hM : ∀ p q, ContDiffOn ℝ n (fun x => M x p q) s) (hu : ∀ p, ContDiffOn ℝ n (fun x => u x p) s)
    (hv : ∀ p, ContDiffOn ℝ n (fun x => v x p) s) :
    ContDiffOn ℝ n (fun x => (star (u x) ⬝ᵥ (M x *ᵥ v x)).re) s := by
  have h : ContDiffOn ℝ n (fun x => star (u x) ⬝ᵥ (M x *ᵥ v x)) s := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    refine ContDiffOn.sum fun p _ => ContDiffOn.mul ?_ (ContDiffOn.sum fun q _ => (hM p q).mul (hv q))
    exact Complex.conjCLE.contDiff.comp_contDiffOn (hu p)
  exact Complex.reCLM.contDiff.comp_contDiffOn h
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
