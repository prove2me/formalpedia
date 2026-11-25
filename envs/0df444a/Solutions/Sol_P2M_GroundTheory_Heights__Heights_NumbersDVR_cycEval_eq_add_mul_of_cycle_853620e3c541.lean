-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_cycle_853620e3c541
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:59.435548+00:00
-- url     : https://prove2.me/submissions/88769d97-8613-4c40-a654-9ccfe5a3fb66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalEqAddMulOfCycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (φ : Ideal (MRing ι R) → ℤ) {Z₀ Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (h₀ : (Function.support Z₀).Finite) (h₂ : (Function.support Z₂).Finite)
    (h : ∀ W, Z₁ W = Z₀ W + k * Z₂ W) :
    cycEval φ Z₁ = cycEval φ Z₀ + k * cycEval φ Z₂ := by
  unfold cycEval
  have f₀ : (Function.support fun W => Z₀ W * φ W).Finite :=
    h₀.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => k * (Z₂ W * φ W)).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [mul_finsum, ← finsum_add_distrib f₀ f₂]
  refine finsum_congr fun W => ?_
  rw [h W]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR
