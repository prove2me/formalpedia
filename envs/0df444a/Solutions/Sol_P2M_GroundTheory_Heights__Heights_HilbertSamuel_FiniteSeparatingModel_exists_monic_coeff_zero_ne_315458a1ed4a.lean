-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_monic_coeff_zero_ne_315458a1ed4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:39.44423+00:00
-- url     : https://prove2.me/submissions/2454d541-a925-4183-a4cd-ae07200d6916

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
theorem _root_.solution {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) {f : MvPolynomial σ ℚ} (hf : f ∉ P)
    {p : Polynomial (MvPolynomial (Fin e) ℚ)} (hp : p.Monic) (hpf : p.eval₂ (aeval ℓ).toRingHom f ∈ P) :
    ∃ q : Polynomial (MvPolynomial (Fin e) ℚ),
      q.Monic ∧ q.eval₂ (aeval ℓ).toRingHom f ∈ P ∧ q.coeff 0 ≠ 0 := by
  obtain ⟨q, hpq, hdvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hdvd
  refine ⟨q, ?_, ?_, fun h => hdvd (Polynomial.X_dvd_iff.mpr h)⟩
  · rw [hpq] at hp
    exact (Polynomial.monic_X.pow _).of_mul_monic_left hp
  · rw [hpq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hpf
    exact (hP.mem_or_mem hpf).resolve_left fun h => hf (hP.mem_of_pow_mem _ h)
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
