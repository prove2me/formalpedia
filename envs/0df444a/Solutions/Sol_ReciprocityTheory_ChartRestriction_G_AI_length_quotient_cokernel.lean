-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_quotient_cokernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:26.943027+00:00
-- url     : https://prove2.me/submissions/9f55d84c-ebe5-4878-917c-b1a8b33436ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthTwoGeneratorQuotient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_quot_restrict


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
universe u
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (a b : A) :
    length (A ⧸ Ideal.span {a}) ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))) =
      length A (A ⧸ Ideal.span {a, b}) := by
  rw [length_quot_restrict a]
  set N := LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)) with hN
  let f : A →ₗ[A] ((A ⧸ Ideal.span {a}) ⧸ N) :=
    (N.mkQ.restrictScalars A) ∘ₗ (Ideal.span {a} : Ideal A).mkQ
  have hf : Function.Surjective f :=
    (Submodule.mkQ_surjective N).comp (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker f = Ideal.span {a, b} := by
    ext x
    have h1 : x ∈ LinearMap.ker f ↔ Ideal.Quotient.mk (Ideal.span {a}) x ∈ N := by
      rw [LinearMap.mem_ker]
      exact Submodule.Quotient.mk_eq_zero N
    rw [h1, Ideal.mem_span_pair, hN, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [LinearMap.lsmul_apply, smul_eq_mul, ← map_mul, Ideal.Quotient.eq,
        Ideal.mem_span_singleton'] at hy
      obtain ⟨c, hc⟩ := hy
      exact ⟨-c, y, by linear_combination -hc⟩
    · rintro ⟨c, y, h⟩
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      rw [LinearMap.lsmul_apply, smul_eq_mul, ← map_mul, Ideal.Quotient.eq,
        Ideal.mem_span_singleton']
      exact ⟨-c, by linear_combination -h⟩
  exact ((f.quotKerEquivOfSurjective hf).symm.trans
    (Submodule.quotEquivOfEq _ _ hk)).length_eq
end ReciprocityTheory.ChartRestriction.G.AI
