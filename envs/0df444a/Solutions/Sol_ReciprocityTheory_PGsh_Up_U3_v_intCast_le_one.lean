-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.v_intCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:57.667801+00:00
-- url     : https://prove2.me/submissions/f25992af-baea-4b63-aab1-041d0189f800

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
theorem _root_.solution (hv : v.Integers R) (n : ℤ) : v (n : C) ≤ 1 := by
  rw [← map_intCast (algebraMap R C) n]
  exact hv.map_le_one _
end ReciprocityTheory.PGsh.Up.U3
