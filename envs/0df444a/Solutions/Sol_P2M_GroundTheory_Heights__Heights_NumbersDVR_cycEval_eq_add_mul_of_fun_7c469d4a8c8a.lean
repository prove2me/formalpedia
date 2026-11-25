-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_fun_7c469d4a8c8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:00.437001+00:00
-- url     : https://prove2.me/submissions/48490247-c08d-4363-96dd-5636fcc0e1f1

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
theorem _root_.solution {φ₀ φ₁ φ₂ : Ideal (MRing ι R) → ℤ} {Z : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (hZ : (Function.support Z).Finite) (h : ∀ W, Z W ≠ 0 → φ₁ W = φ₀ W + k * φ₂ W) :
    cycEval φ₁ Z = cycEval φ₀ Z + k * cycEval φ₂ Z := by
  unfold cycEval
  have f₀ : (Function.support fun W => Z W * φ₀ W).Finite :=
    hZ.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => k * (Z W * φ₂ W)).Finite :=
    hZ.subset fun W hW h0 => hW (by simp [h0])
  rw [mul_finsum, ← finsum_add_distrib f₀ f₂]
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW]
    ring
end GroundTheory.Heights₂.Heights.NumbersDVR
