-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_degree_line_indep_855d717e1a04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:11:33.297643+00:00
-- url     : https://prove2.me/submissions/d44f1a7a-a70b-4615-8580-ae328847c48d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermitianMetric K E) (hE : Module.finrank (𝓞 K) E = 1) {s t : E}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) {s})) - ∑ σ : K →+* ℂ, Real.log ‖fibreVec h σ s‖ =
      Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) {t})) -
        ∑ σ : K →+* ℂ, Real.log ‖fibreVec h σ t‖ := by
  rw [← arithDegree_line h hE hs, ← arithDegree_line h hE ht]
end GroundTheory.Heights₂.Heights
