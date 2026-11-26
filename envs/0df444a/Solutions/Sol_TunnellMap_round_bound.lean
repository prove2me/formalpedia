-- Prove2me | solution 1 for TunnellMap.round_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:49:33.236705+00:00
-- url     : https://prove2.me/submissions/0263fee0-8758-4cbf-a102-c8c289e5ff82

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution {a b : ℤ} (ha : 0 < a) :
    -a ≤ 2 * (b - nearestQuot b a * a) ∧ 2 * (b - nearestQuot b a * a) ≤ a := by
  unfold nearestQuot
  by_cases hb : 0 ≤ b
  · rw [if_pos hb]
    have hdiv := Int.mul_ediv_add_emod (2 * b + a - 1) (2 * a)
    have hlo : 0 ≤ (2 * b + a - 1) % (2 * a) := Int.emod_nonneg _ (by omega)
    have hhi : (2 * b + a - 1) % (2 * a) < 2 * a := Int.emod_lt_of_pos _ (by omega)
    generalize (2 * b + a - 1) / (2 * a) = Q at *
    generalize (2 * b + a - 1) % (2 * a) = R at *
    constructor <;> nlinarith
  · rw [if_neg hb]
    have hdiv := Int.mul_ediv_add_emod (-(2 * b) + a - 1) (2 * a)
    have hlo : 0 ≤ (-(2 * b) + a - 1) % (2 * a) := Int.emod_nonneg _ (by omega)
    have hhi : (-(2 * b) + a - 1) % (2 * a) < 2 * a := Int.emod_lt_of_pos _ (by omega)
    generalize (-(2 * b) + a - 1) / (2 * a) = Q at *
    generalize (-(2 * b) + a - 1) % (2 * a) = R at *
    constructor <;> nlinarith
end TunnellMap
