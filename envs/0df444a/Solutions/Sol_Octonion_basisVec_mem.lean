-- Prove2me | solution 1 for Octonion.basisVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:54.12673+00:00
-- url     : https://prove2.me/submissions/fbfbf61f-a7fb-4e3e-a4d3-722511c0b9af

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

/-- Each coordinate unit `eₖ` (the `k`-th standard Gravesian basis vector) is a Cayley integer:
its doubled coordinate vector is `2 eₖ`, of even parity pattern (mask `0`). -/
theorem solution (k : Fin 8) : Octonion.basisVec k ∈ Octonion.cayleyIntegers := by
  rw [Octonion.mem_cayleyIntegers]
  refine ⟨fun i => if i = k then 2 else 0, rfl, ?_⟩
  refine Finset.mem_image.mpr ⟨0, by decide, ?_⟩
  rw [Octonion.patOfMask_zero]
  ext i
  by_cases h : i = k <;> simp [h]

namespace Octonion






end Octonion
