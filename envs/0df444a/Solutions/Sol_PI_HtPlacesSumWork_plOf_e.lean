-- Prove2me | solution 1 for PI.HtPlacesSumWork.plOf_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:50.228817+00:00
-- url     : https://prove2.me/submissions/3192d10d-201a-47ea-bdd3-b8d0aa3bca75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_addv_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]
namespace PI.HtPlacesSumWork
theorem _root_.solution (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) {ϖ : O}
    (hϖ : Irreducible ϖ) :
    plOf O L Q (algebraMap O L ϖ) = (((Q.1.ramificationIdx O : ℕ) : ℤ) : WithTop ℤ) := by
  have := Q.2
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure O L) L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact FaithfulSMul.algebraMap_injective O L
  have hb0 : algebraMap O (integralClosure O L) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  haveI : Q.1.LiesOver (maximalIdeal O) := ⟨(valPl_comap Q.1).symm⟩
  have hmap : Ideal.map (algebraMap O (integralClosure O L)) (maximalIdeal O) =
      Ideal.span {algebraMap O (integralClosure O L) ϖ} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span, Set.image_singleton]
  have hne : Ideal.map (algebraMap O (integralClosure O L)) (maximalIdeal O) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hb0
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (maximalIdeal O) Q.1 hne, hmap]
  rw [plOf, IsScalarTower.algebraMap_apply O (integralClosure O L) L, addv_alg _ hb0,
    HeightOneSpectrum.intValuation_if_neg _ hb0, log_exp, neg_neg]
  have hc := Ideal.count_associates_factors_eq (I := Ideal.span {algebraMap O (integralClosure O L) ϖ})
    (J := Q.1) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0) Q.2.isPrime
    (valPl_ne_bot Q.1)
  exact congrArg (fun n : ℕ => (((n : ℤ)) : WithTop ℤ)) hc
end PI.HtPlacesSumWork
