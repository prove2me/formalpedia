-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.Dkl_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:59.242678+00:00
-- url     : https://prove2.me/submissions/9cd17530-53c5-40bf-a1a7-76d8ede58dbb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Differentiable ℝ (F i))
    (k l : Fin n) : Dkl k l (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * Dkl k l (F i) y := by
  funext y
  unfold Dkl dirC
  have hfun : (fun y => ∑ i ∈ s, c i * F i y) = ∑ i ∈ s, (fun y => c i * F i y) := by
    funext y; simp [Finset.sum_apply]
  rw [hfun, fderiv_sum (fun i hi => ((hF i hi) y).const_mul (c i))]
  have e : ∀ i ∈ s, fderiv ℝ (fun y => c i * F i y) y = c i • fderiv ℝ (F i) y :=
    fun i hi => fderiv_const_mul ((hF i hi) y) (c i)
  rw [Finset.sum_congr rfl e]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring
end PositivityTheory.Rg.Sw.WR.T
