-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.res_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:43.819428+00:00
-- url     : https://prove2.me/submissions/3b7dfe4d-56d8-4fde-be9d-d5dd855e506f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (hv : v.Integers R) (r : R) : res hv r = 0 ↔ v (algebraMap R C r) < 1 :=
  Ideal.Quotient.eq_zero_iff_mem
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
