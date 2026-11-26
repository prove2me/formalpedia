-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qBinom_cast_eq_qFactorial_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:51.195798+00:00
-- url     : https://prove2.me/submissions/5cfd5dff-08cc-4b54-88ab-02ec7ad14668

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_mul_qFactorials

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    (qBinom q n k : ℚ) =
      qFactorial q n / (qFactorial q k * qFactorial q (n - k)) := by
  have hden : (qFactorial q k * qFactorial q (n - k) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Nat.mul_pos (qFactorial_pos hq k) (qFactorial_pos hq (n - k))))
  apply (eq_div_iff hden).2
  simpa [mul_assoc] using (show
    (qBinom q n k : ℚ) * (qFactorial q k : ℚ) *
      (qFactorial q (n - k) : ℚ) = (qFactorial q n : ℚ) by
        exact_mod_cast qBinom_mul_qFactorials hq hk)
end SharpIntermediateSubgroupBounds
