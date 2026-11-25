-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.mem_augIdeal_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:40:53.284842+00:00
-- url     : https://prove2.me/submissions/a879c527-db62-4e20-b9cc-dac625c07bab

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) (f : X → C) :
    f ∈ augIdeal (hopfPull e A).carrier ↔ (pbE (C := C) (R := R) e).symm f ∈ augIdeal A.carrier := by
  rw [show (hopfPull e A).carrier =
      A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) from rfl]
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply,
    Submodule.mem_map_equiv, pbE_symm_apply, map_zero]
end ReciprocityTheory.PGsh.Up
