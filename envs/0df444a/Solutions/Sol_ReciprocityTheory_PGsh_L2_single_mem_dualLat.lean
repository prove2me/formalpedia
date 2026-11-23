-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.single_mem_dualLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:58.374941+00:00
-- url     : https://prove2.me/submissions/e27d8ca7-67d5-45b2-a0c4-37cc24078939

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
private theorem mem_dualLat_iff_sum_mul_integral {X : Type} [Fintype X] (M : Submodule R (X → C)) (u : X → C) :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (AA : HopfOrder (C := C) R N) :
    (Pi.single 0 1 : N → C) ∈ dualLat AA.carrier := by
  rw [mem_dualLat_iff_sum_mul_integral]
  intro f hf
  obtain ⟨r, hr⟩ := AA.le_int hf 0
  refine ⟨r, ?_⟩
  rw [hr]
  simp [Pi.single_apply]
end ReciprocityTheory.PGsh.L2
