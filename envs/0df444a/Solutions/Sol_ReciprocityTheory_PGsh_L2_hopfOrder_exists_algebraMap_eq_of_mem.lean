-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.hopfOrder_exists_algebraMap_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:52.883638+00:00
-- url     : https://prove2.me/submissions/2372d189-cfd3-4cba-8674-50fbbb34b73f

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (AA : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ AA.carrier) (x : N) :
    ∃ r : R, algebraMap R C r = f x := by
  exact AA.le_int hf x
end ReciprocityTheory.PGsh.L2
