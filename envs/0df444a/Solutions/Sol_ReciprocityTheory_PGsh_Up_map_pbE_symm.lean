-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.map_pbE_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:40:45.252891+00:00
-- url     : https://prove2.me/submissions/e3614b28-b7c2-4870-a0af-9f158657b5bb

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
theorem _root_.solution (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))).map (pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)) = M := by
  rw [← Submodule.map_comp]
  have h : ((pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)).comp
      (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) = LinearMap.id := by
    refine LinearMap.ext fun f => funext fun y => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pbE_apply, LinearMap.id_apply,
      AddEquiv.apply_symm_apply]
  rw [h, Submodule.map_id]
end ReciprocityTheory.PGsh.Up
