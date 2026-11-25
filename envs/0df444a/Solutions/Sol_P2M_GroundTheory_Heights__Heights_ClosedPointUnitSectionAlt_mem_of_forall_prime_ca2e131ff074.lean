-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_forall_prime_ca2e131ff074
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:07.297517+00:00
-- url     : https://prove2.me/submissions/6ba0835c-743d-4c8c-b825-011ae3683ff8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_mul_5d9adfcd55aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_isIntegral_0419822bff1d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (W : ValuationSubring K')
    (hW : ∀ q : ℕ, q.Prime → W.valuation (q : K') = 1) (x : K') : x ∈ W := by
  have hN : ∀ N : ℕ, N ≠ 0 → W.valuation (N : K') = 1 := by
    intro N
    induction N using Nat.recOnMul with
    | zero => exact fun h => (h rfl).elim
    | one => intro; simp
    | prime p hp => intro; exact hW p hp
    | mul a b ha hb =>
      intro h
      rw [Nat.cast_mul, map_mul, ha (left_ne_zero_of_mul h), hb (right_ne_zero_of_mul h), one_mul]
  obtain ⟨n, hn, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K').mpr (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  have h1 := mem_of_isIntegral W hint
  rw [zsmul_eq_mul] at h1
  have hv : W.valuation (n : K') = 1 := by
    have h2 := hN _ (Int.natAbs_ne_zero.mpr hn)
    rcases Int.natAbs_eq n with h | h
    · rw [h, Int.cast_natCast]
      exact h2
    · rw [h, Int.cast_neg, Valuation.map_neg, Int.cast_natCast]
      exact h2
  rw [← W.valuation_le_one_iff] at h1 ⊢
  rwa [map_mul, hv, one_mul] at h1
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
