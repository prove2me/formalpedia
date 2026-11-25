-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.res_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:45.197772+00:00
-- url     : https://prove2.me/submissions/7be4f436-b346-4851-a4e8-9d38995c5dc2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_res_eq_zero

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
theorem _root_.solution (hv : v.Integers R) (r : R) : res hv r ≠ 0 ↔ v (algebraMap R C r) = 1 := by
  rw [Ne, res_eq_zero, v_eq_one_iff hv, mem_mI]
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
