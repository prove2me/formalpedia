-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Ylb4.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:03:31.596248+00:00
-- url     : https://prove2.me/submissions/558d6717-f333-46a8-8fec-8b2897df4123

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideSide

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Ylb4
theorem _root_.solution :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] {N : ℕ} {P Q B : Matrix (Fin N) (Fin N) k}
      {C : ValuativeRel.ValueGroupWithZero k},
      (∀ (i j : Fin N),
          (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (P i j) ≤
            (1 : ValuativeRel.ValueGroupWithZero k)) →
        (∀ (i j : Fin N),
            (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (Q i j) ≤
              (1 : ValuativeRel.ValueGroupWithZero k)) →
          (∀ (i j : Fin N), (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (B i j) ≤ C) →
            ∀ (i j : Fin N), (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) ((P * B * Q) i j) ≤ C := by
  intro k _ _ N P Q B C hP hQ hB i j
  have hPB : ∀ a b : Fin N, ValuativeRel.valuation k ((P * B) a b) ≤ C := by
    intro a b
    rw [Matrix.mul_apply]
    apply Valuation.map_sum_le
    intro m _
    rw [Valuation.map_mul]
    calc ValuativeRel.valuation k (P a m) * ValuativeRel.valuation k (B m b)
        ≤ 1 * C := mul_le_mul' (hP a m) (hB m b)
      _ = C := one_mul C
  rw [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [Valuation.map_mul]
  calc ValuativeRel.valuation k ((P * B) i l) * ValuativeRel.valuation k (Q l j)
      ≤ C * 1 := mul_le_mul' (hPB i l) (hQ l j)
    _ = C := mul_one C
end UpperTheory.Reformulated.B.Ylb4
