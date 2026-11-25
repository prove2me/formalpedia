-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_minpoly_426ccccab7a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:37.936313+00:00
-- url     : https://prove2.me/submissions/97be5cb8-ae4d-4bbe-8627-2bf2ffe60632

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsNoetherProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiniteSeparatingModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
variable {σ : Type} {e : ℕ}
set_option synthInstance.maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
theorem _root_.solution {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) (hinj : ∀ q : MvPolynomial (Fin e) ℚ, aeval ℓ q ∈ P → q = 0)
    (hint : ∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
      p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P) (u : MvPolynomial σ ℚ) :
    ∃ G : Polynomial (MvPolynomial (Fin e) ℚ), G.Monic ∧ G.eval₂ (aeval ℓ).toRingHom u ∈ P ∧
      ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Q.eval₂ (aeval ℓ).toRingHom u ∈ P → G ∣ Q := by
  let φ : MvPolynomial (Fin e) ℚ →+* MvPolynomial σ ℚ ⧸ P :=
    (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom
  let _ : Algebra (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P) := φ.toAlgebra
  have key : ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ),
      Polynomial.aeval (Ideal.Quotient.mk P u) Q = Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u) :=
    fun Q => by rw [Polynomial.aeval_def, Polynomial.hom_eval₂]; rfl
  have hφ : Function.Injective (algebraMap (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    exact hinj q (Ideal.Quotient.eq_zero_iff_mem.mp hq)
  have : Module.IsTorsionFree (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  obtain ⟨p, hpm, hp⟩ := hint u
  have hu : IsIntegral (MvPolynomial (Fin e) ℚ) (Ideal.Quotient.mk P u) :=
    ⟨p, hpm, by rw [← Polynomial.aeval_def, key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hp⟩
  refine ⟨minpoly _ (Ideal.Quotient.mk P u), minpoly.monic hu, ?_, fun Q hQ => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← key]
    exact minpoly.aeval _ _
  · exact minpoly.isIntegrallyClosed_dvd hu (by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hQ)
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
