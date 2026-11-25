-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integralClosureRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:05:55.831217+00:00
-- url     : https://prove2.me/submissions/a736d1af-c66a-49ab-ba2e-4873776bb889

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L] :
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L := by
  set C := integralClosure O L
  haveI hD : IsDedekindDomain C := integralClosure.isDedekindDomain O F L
  haveI hFin : Module.Finite O C := IsIntegralClosure.finite O F L C
  haveI : Module.IsTorsionFree O L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  haveI : Module.IsTorsionFree O C := inferInstance
  haveI hFr : Module.Free O C := Module.free_of_finite_type_torsion_free'
  haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension O F L C
  set m := IsLocalRing.maximalIdeal O
  have hm : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have key : ∀ Q : Ideal C, Q.IsMaximal ↔ Q ∈ IsDedekindDomain.primesOverFinset m C := by
    intro Q
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C]
    constructor
    · intro hQ
      have hu : (Q.under O).IsMaximal := Ideal.IsMaximal.under O Q
      refine ⟨hQ.isPrime, ⟨?_⟩⟩
      exact (IsLocalRing.eq_maximalIdeal hu).symm
    · rintro ⟨hP, hl⟩
      refine hP.isMaximal ?_
      rintro rfl
      apply hm
      rw [hl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O C)
  refine ⟨hD, hFin, hFr, IsIntegralClosure.rank O F L C, ?_, ?_⟩
  · exact (IsDedekindDomain.primesOverFinset m C).finite_toSet.subset fun Q hQ => (key Q).1 hQ
  · rw [← Ideal.sum_ramification_inertia C F L hm]
    rw [← finsum_comp_equiv (Equiv.subtypeEquivRight key).symm, finsum_eq_sum_of_fintype,
      ← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset m C)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.2
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C] at hP
    haveI := hP.1
    haveI := hP.2
    haveI : P.1.IsMaximal := ((key P.1).2 P.2)
    simp only [Equiv.subtypeEquivRight_symm_apply_coe]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' m P.1 hm, Ideal.inertiaDeg_eq_inertiaDeg' m P.1]
end ReciprocityTheory.MultiplicativeHeights
