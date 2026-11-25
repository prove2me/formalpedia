-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.card_GL_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:17.490525+00:00
-- url     : https://prove2.me/submissions/71aba178-2682-44d4-8187-36978a8d2840

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_SpanIsMaximal
import Theorems.Thm_PI_ParahoricIdxZ_W_prod_Icc_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
namespace PI.ParahoricIdxZ.W
theorem _root_.solution (k : Type) [Field k] [Fintype k] (n : ℕ) :
    (Nat.card (GL (Fin n) k) : ℝ) = (Fintype.card k : ℝ) ^ (n * n) * qE (Fintype.card k) 1 n := by
  rw [Matrix.card_GL_field]
  have hq : 1 ≤ Fintype.card k := Fintype.card_pos
  have hq0 : (Fintype.card k : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range
    (fun i => ((Fintype.card k ^ n - Fintype.card k ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hfac : ∀ j ∈ range n, ((Fintype.card k ^ n - Fintype.card k ^ (n - 1 - j) : ℕ) : ℝ) =
      (Fintype.card k : ℝ) ^ n * (1 - (Fintype.card k : ℝ) ^ (-((j + 1 : ℕ) : ℤ))) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
    push_cast
    rw [mul_sub, mul_one]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0]
    congr 1
    omega
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul, qE, prod_Icc_one]
end PI.ParahoricIdxZ.W
