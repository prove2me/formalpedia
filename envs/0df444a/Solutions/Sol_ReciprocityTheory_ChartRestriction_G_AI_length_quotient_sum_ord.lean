-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_quotient_sum_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:34.203697+00:00
-- url     : https://prove2.me/submissions/e4ef54f1-db4e-47b6-91f1-41c7c4e2e7af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthTwoGeneratorQuotient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_dim_quot_comap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_height_one_iff_dim_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_loc_quot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ordMod_quot


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
theorem _root_.solution (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (b : A) :
    (∑ᶠ (P : PrimeSpectrum (A ⧸ Ideal.span {a}))
        (_ : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1),
        length (Localization.AtPrime P.asIdeal)
          (LocalizedModule P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) *
            ordMod P (Ideal.Quotient.mk (Ideal.span {a}) b)) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b := by
  have hmem : ∀ P : PrimeSpectrum (A ⧸ Ideal.span {a}),
      a ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal := by
    intro P
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)]
    exact zero_mem _
  refine finsum_mem_eq_of_bijOn
    (s := {P : PrimeSpectrum (A ⧸ Ideal.span {a}) |
      ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1})
    (t := {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal})
    (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) ⟨?_, ?_, ?_⟩ ?_
  · intro P hP
    refine ⟨(height_one_iff_dim_one h2 ha _ (hmem P)).2 ?_, hmem P⟩
    rw [← dim_quot_comap]
    exact hP
  · exact (PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).injOn
  · rintro p ⟨hp, hap⟩
    have : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
      exact (Ideal.span_singleton_le_iff_mem _).2 hap
    obtain ⟨P, rfl⟩ := this
    refine ⟨P, ?_, rfl⟩
    change ringKrullDim _ = 1
    rw [dim_quot_comap]
    exact (height_one_iff_dim_one h2 ha _ hap).1 hp
  · intro P _
    rw [length_loc_quot, ordMod_quot]
end ReciprocityTheory.ChartRestriction.G.AI
