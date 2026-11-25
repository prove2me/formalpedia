-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_sum_fin_pow_26f64c5d5481
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:39.438731+00:00
-- url     : https://prove2.me/submissions/a82c0ff1-51e4-4f60-b5d3-f69f7d7ab833

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootGridLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootGridLower

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
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootGridLower
theorem _root_.solution {M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    {a b : ℕ} (ha : a < M) (hb : b < M) :
    ∑ t : Fin M, (ω ^ a * (ω ^ b)⁻¹) ^ (t : ℕ) = if a = b then (M : ℂ) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero hM.ne'
  rw [Fin.sum_univ_eq_sum_range (fun t => (ω ^ a * (ω ^ b)⁻¹) ^ t)]
  split_ifs with hab
  · subst hab
    simp [mul_inv_cancel₀ (pow_ne_zero _ hω0)]
  · have hz : ω ^ a * (ω ^ b)⁻¹ ≠ 1 := by
      intro h
      apply hab
      apply hω.pow_inj ha hb
      have := congrArg (· * ω ^ b) h
      simpa [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hω0)] using this
    rw [geom_sum_eq hz]
    have h1 : (ω ^ a * (ω ^ b)⁻¹) ^ M = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    simp [h1]
end RootGridLower
end GroundTheory.Heights₂.Heights.HilbertSamuel
