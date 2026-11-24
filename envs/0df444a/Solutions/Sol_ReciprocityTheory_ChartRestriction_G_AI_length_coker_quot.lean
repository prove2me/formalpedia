-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_coker_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:04.993801+00:00
-- url     : https://prove2.me/submissions/088a5146-b4b7-43c6-ab61-3547774b705c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (q : PrimeSpectrum A) (x : A) :
    length A ((A ⧸ q.asIdeal) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ q.asIdeal) x)) =
      ordMod q x := by
  have hr : LinearMap.range (LinearMap.lsmul A (A ⧸ q.asIdeal) x) =
      (Ideal.span {Ideal.Quotient.mk q.asIdeal x}).restrictScalars A := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm]⟩
  rw [(Submodule.quotEquivOfEq _ _ hr).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A _).length_eq,
    Module.length_eq_of_surjective (S := A) (R := A ⧸ q.asIdeal) Ideal.Quotient.mk_surjective]
  rfl
end ReciprocityTheory.ChartRestriction.G.AI
