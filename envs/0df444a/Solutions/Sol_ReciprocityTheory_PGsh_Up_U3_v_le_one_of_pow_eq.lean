-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.v_le_one_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:17.309884+00:00
-- url     : https://prove2.me/submissions/702a7637-c9bf-4930-9cc9-9e6ad310e6a0

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution {r : C} (hr : r ^ p = r) : v r ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : 2 ≤ p := hp.out.two_le
  have key : v r ^ 1 < v r ^ p := pow_lt_pow_right₀ h (by omega)
  rw [pow_one, ← map_pow, hr] at key
  exact lt_irrefl _ key
end ReciprocityTheory.PGsh.Up.U3
