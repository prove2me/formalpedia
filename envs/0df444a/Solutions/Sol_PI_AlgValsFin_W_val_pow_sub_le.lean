-- Prove2me | solution 1 for PI.AlgValsFin.W.val_pow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:02:58.41292+00:00
-- url     : https://prove2.me/submissions/44dd2e3c-d29e-45eb-8b2a-b6d26c7312cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
namespace PI.AlgValsFin.W
theorem _root_.solution {x b : v.adicCompletion L} (hx : Valued.v x ≤ 1) (hb : Valued.v b ≤ 1) (k : ℕ) :
    Valued.v (x ^ k - b ^ k) ≤ Valued.v (x - b) := by
  have key : x ^ k - b ^ k = (∑ i ∈ Finset.range k, x ^ i * b ^ (k - 1 - i)) * (x - b) :=
    (geom_sum₂_mul x b k).symm
  rw [key, map_mul]
  have hs : Valued.v (∑ i ∈ Finset.range k, x ^ i * b ^ (k - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one₀ zero_le' hx) (pow_le_one₀ zero_le' hb)
  exact mul_le_of_le_one_left' hs
end PI.AlgValsFin.W
