-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_summable_signed_609d30551a2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:52:39.822525+00:00
-- url     : https://prove2.me/submissions/55eeb222-eeb3-4a76-a90f-3e54fc4628c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealTransferOfSyzygy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
namespace GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
theorem _root_.solution (p : ℕ) (hp : 2 ≤ p) (k : ℕ) (hk : 1 ≤ k) (R : ℚ) (ε : ℕ → ℚ)
    (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    Summable (fun n : ℕ => ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((ε n * R : ℚ) : ℝ)) := by
  set q : ℝ := ((p : ℝ) ^ k)⁻¹ with hq
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 (by omega))
  have hpow : ∀ n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ = q * q ^ n := fun n => by
    rw [hq, ← pow_succ', mul_comm, pow_mul, inv_pow]
  refine Summable.of_norm_bounded (g := fun n => q * q ^ n * |(R : ℝ)|)
    (((summable_geometric_of_lt_one hq0 hq1).mul_left q).mul_right _) (fun n => ?_)
  rw [hpow, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]
  rcases hε n with h | h <;> simp [h]
end GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
