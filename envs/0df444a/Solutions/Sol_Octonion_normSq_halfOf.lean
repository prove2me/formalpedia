-- Prove2me | solution 1 for Octonion.normSq_halfOf
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:31:13.704328+00:00
-- url     : https://prove2.me/submissions/5cae2c2e-6471-4d76-ac3a-821cdf763338

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

open Quaternion BigOperators

namespace Octonion

end Octonion

open Octonion

/-- The norm of a half-vector is a quarter of the integer square sum: `N (a/2) = (Σ aᵢ²)/4`.
Proved over opaque quaternion halves (`set` + `rfl` coordinate facts): rewriting `normSq` at an
unfolded quaternion literal leaves terms not type-correct at reducible transparency. -/
theorem solution (a : Fin 8 → ℤ) :
    Octonion.normSq (Octonion.halfOf a) = (∑ i : Fin 8, ((a i : ℚ))^2) / 4 := by
  set p : ℍ[ℚ] := (Octonion.halfOf a).fst
  set q : ℍ[ℚ] := (Octonion.halfOf a).snd
  have hsum : Octonion.normSq (Octonion.halfOf a) = Quaternion.normSq p + Quaternion.normSq q := rfl
  rw [hsum, Quaternion.normSq_def', Quaternion.normSq_def']
  have e0 : p.1 = (a 0 : ℚ) / 2 := rfl
  have e1 : p.2 = (a 1 : ℚ) / 2 := rfl
  have e2 : p.3 = (a 2 : ℚ) / 2 := rfl
  have e3 : p.4 = (a 3 : ℚ) / 2 := rfl
  have e4 : q.1 = (a 4 : ℚ) / 2 := rfl
  have e5 : q.2 = (a 5 : ℚ) / 2 := rfl
  have e6 : q.3 = (a 6 : ℚ) / 2 := rfl
  have e7 : q.4 = (a 7 : ℚ) / 2 := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  rw [Fin.sum_univ_eight]
  field_simp
  ring

namespace Octonion


end Octonion
