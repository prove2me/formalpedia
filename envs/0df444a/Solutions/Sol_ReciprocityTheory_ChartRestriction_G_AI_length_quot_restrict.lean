-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_quot_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:05.735021+00:00
-- url     : https://prove2.me/submissions/0515a6b5-1454-4e2c-90bd-1eb5856b7b31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
universe u v
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (a : A) (N : Type v) [AddCommGroup N] [Module (A ⧸ Ideal.span {a}) N]
    [Module A N] [IsScalarTower A (A ⧸ Ideal.span {a}) N] :
    length (A ⧸ Ideal.span {a}) N = length A N := by
  have hsmul : ∀ (r : A) (n : N), Ideal.Quotient.mk (Ideal.span {a}) r • n = r • n := fun r n => by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul (A ⧸ Ideal.span {a})]
  let g : Submodule A N → Submodule (A ⧸ Ideal.span {a}) N := fun p =>
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun c n hn => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [hsmul]
        exact p.smul_mem r hn }
  let iso : Submodule (A ⧸ Ideal.span {a}) N ≃o Submodule A N :=
    { toFun := fun p => p.restrictScalars A
      invFun := g
      left_inv := fun p => by ext; rfl
      right_inv := fun p => by ext; rfl
      map_rel_iff' := by
        intro p q
        exact Submodule.restrictScalars_le A }
  have h : Order.krullDim (Submodule (A ⧸ Ideal.span {a}) N) = Order.krullDim (Submodule A N) :=
    le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
      (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
  unfold Module.length
  first
    | simp only [h]
    | congr 1
end ReciprocityTheory.ChartRestriction.G.AI
