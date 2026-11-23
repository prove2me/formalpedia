-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValUFD.heightOne_principal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:51.730135+00:00
-- url     : https://prove2.me/submissions/459e0497-98d4-4bb9-a2c8-c810d4ad77dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValUFD
variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
namespace ReciprocityTheory.ChartRestriction.G.T0.ValUFD
theorem _root_.solution (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ g : R, Prime g ∧ p = Ideal.span {g} := by
  have hpr := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp
  have hsp : Ideal.span {Submodule.IsPrincipal.generator p} = p :=
    Submodule.IsPrincipal.span_singleton_generator p
  have hne : Submodule.IsPrincipal.generator p ≠ 0 := fun h0 =>
    p.ne_bot_of_height_eq_one hp ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)
  refine ⟨_, (Ideal.span_singleton_prime hne).mp (by rw [hsp]; infer_instance), hsp.symm⟩
end ReciprocityTheory.ChartRestriction.G.T0.ValUFD
