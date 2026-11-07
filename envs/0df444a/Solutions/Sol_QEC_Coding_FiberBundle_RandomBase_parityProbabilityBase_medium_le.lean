-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_medium_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:08:19.410717+00:00
-- url     : https://prove2.me/submissions/b6691a45-aadf-48e5-ad69-dae31b7d2e16

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exp_neg_two_mul_le_inv_one_add_two_mul
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_le_expEnvelope


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (p : Real) (w : Nat) (hp0 : 0 ≤ p) (hpHalf : p ≤ 1 / 2)
    (hmedium : p * w ≤ 3) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      Real.exp (-(p * w) / 7) := by
  let x : Real := p * w
  have hx0 : 0 ≤ x := by positivity
  have hx3 : x ≤ 3 := hmedium
  have hden : 0 < 1 + 2 * x := by positivity
  calc
    _ ≤ (1 + Real.exp (-2 * x)) / 2 :=
      parityProbabilityBase_le_expEnvelope p w hpHalf
    _ ≤ (1 + 1 / (1 + 2 * x)) / 2 := by
      gcongr
      exact exp_neg_two_mul_le_inv_one_add_two_mul x hx0
    _ = (1 + x) / (1 + 2 * x) := by
      field_simp
      ring
    _ ≤ 1 - x / 7 := by
      rw [div_le_iff₀ hden]
      nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx3)]
    _ ≤ Real.exp (-x / 7) := by
      linarith [Real.add_one_le_exp (-x / 7)]
end QEC.Coding.FiberBundle.RandomBase
