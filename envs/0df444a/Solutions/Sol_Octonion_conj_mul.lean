-- Prove2me | solution 1 for Octonion.conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:56.604728+00:00
-- url     : https://prove2.me/submissions/946a352e-d5af-4b9e-b859-0061a3bc3fc2

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Quaternion

namespace Octonion

end Octonion

open Octonion

/-- `x̄ · x = N x`: the conjugate-side companion of `mul_conj`, needed because the octonion
product is not commutative (nor associative). Same coordinate expansion. -/
theorem solution (x : octonions ℚ) : Octonion.conj x * x = ⟨⟨Octonion.normSq x, 0, 0, 0⟩, 0⟩ := by
  obtain ⟨a, b⟩ := x
  refine Octonion.ext_coord8 fun i => ?_
  fin_cases i
  all_goals
    simp only [Octonion.coord8, Octonion.fst_mul, Octonion.snd_mul, Octonion.conj, re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub,
      imJ_sub, imK_sub, re_mul, imI_mul, imJ_mul, imK_mul, re_star, imI_star, imJ_star, imK_star,
      re_neg, imI_neg, imJ_neg, imK_neg, Octonion.normSq, Quaternion.normSq_def']
    simp
    try ring

namespace Octonion


end Octonion
