-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:36.520967+00:00
-- url     : https://prove2.me/submissions/41a7ca7c-b07d-42a9-a8d8-b999665cbc07

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot

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
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Ring.KrullDimLE 1 A] {x : A} (hx : x ≠ 0) :
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ := by
  have htors : Module.IsTorsionBy A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) x := by
    intro n
    refine Submodule.Quotient.induction_on _ n (fun m => ?_)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, rfl⟩
  have htors' : Module.IsTorsionBySet A (M ⧸ LinearMap.range (LinearMap.lsmul A M x))
      (Ideal.span {x} : Set A) :=
    (Module.isTorsionBySet_span_singleton_iff x).mpr htors
  letI : Module (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) := htors'.module
  haveI : IsScalarTower A (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) :=
    htors'.isScalarTower
  haveI : Ring.KrullDimLE 0 (A ⧸ Ideal.span {x}) := by
    rw [Ring.krullDimLE_zero_iff]
    intro P hP
    have hc : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P).IsPrime := Ideal.IsPrime.comap _
    have hne : Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P ≠ ⊥ := by
      intro h0
      have hxm : x ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)]
        exact P.zero_mem
      rw [h0, Ideal.mem_bot] at hxm
      exact hx hxm
    haveI hm := Ideal.IsPrime.isMaximal_of_ne_bot hc hne
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {x})) := Ideal.Quotient.mk_surjective
    have hmap := Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj
      (m := Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P) (by
        intro a ha
        rw [RingHom.mem_ker] at ha
        rw [Ideal.mem_comap, ha]
        exact P.zero_mem)
    rwa [Ideal.map_comap_of_surjective _ hsurj] at hmap
  haveI : IsArtinianRing (A ⧸ Ideal.span {x}) := isArtinianRing_iff_krullDimLE_zero.mpr inferInstance
  haveI : Module.Finite (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hs : Function.Surjective (algebraMap A (A ⧸ Ideal.span {x})) := Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective hs, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, inferInstance⟩
end ReciprocityTheory.ChartRestriction.G.AI
