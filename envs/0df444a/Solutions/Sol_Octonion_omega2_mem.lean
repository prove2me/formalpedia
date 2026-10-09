-- Prove2me | solution 1 for Octonion.omega2_mem
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:33:07.796284+00:00
-- url     : https://prove2.me/submissions/21182ad7-bb50-4877-b970-2833773bf7ee

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace Octonion

/-- Membership in the Cayley integers is exactly the lattice condition `isCayley`: all eight
coordinates lie in `½ℤ` and the parity pattern of the doubled coordinates is a Hamming codeword.
As a `simp` lemma this insulates users from the subring's set representation. -/
@[simp]
theorem mem_cayleyIntegers (x : octonions ℚ) :
    x ∈ cayleyIntegers ↔ isCayley x :=
  Iff.rfl

end Octonion

open Quaternion

namespace Octonion





end Octonion

open Octonion

/-- The half-integral generator `ω₂ = (0, (1 + i + j + k) / 2)` of the second Hurwitz factor is
a Cayley integer (doubled parity mask `240`). Its coordinates `0` and `1` are both zero,
so swapping those coordinates leaves this vector unchanged. -/
theorem solution :
    (⟨0, ⟨(1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩⟩ : octonions ℚ) ∈
      Octonion.cayleyIntegers := by
  rw [Octonion.mem_cayleyIntegers]
  refine ⟨fun i => if i < 4 then 0 else 1, Octonion.ext_coord8 fun i => ?_, ?_⟩
  · fin_cases i <;> simp [Octonion.coord8, Octonion.halfOf]
  · refine Finset.mem_image.mpr ⟨240, by decide, ?_⟩
    ext i
    fin_cases i <;> decide

namespace Octonion


end Octonion
