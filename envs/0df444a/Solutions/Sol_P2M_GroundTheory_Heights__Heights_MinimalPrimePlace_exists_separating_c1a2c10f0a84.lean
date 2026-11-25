-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_separating_c1a2c10f0a84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:17.535823+00:00
-- url     : https://prove2.me/submissions/d57d877a-1844-4fd9-b0fa-51b6e851ab1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_of_le_of_mem_minimalPrimes_a8b5b8aff5b2
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_inf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.MinimalPrimePlace
theorem _root_.solution [IsNoetherianRing A] {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    ∃ s t : A, t ∈ p ∧ s ∉ p ∧ ∀ q ∈ minimalPrimes A, q ≠ p → s ∈ q ∧ t ∉ q := by
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hpP : p.IsPrime := hp.1.1
  have hF : ¬ (hfin.toFinset.erase p).inf id ≤ p := by
    rw [hpP.inf_le']
    rintro ⟨q, hq, hqp⟩
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hq
    exact hq.1 (eq_of_le_of_mem_minimalPrimes hq.2 hp hqp)
  obtain ⟨s, hsF, hsp⟩ := SetLike.not_le_iff_exists.1 hF
  have hsq : ∀ q ∈ minimalPrimes A, q ≠ p → s ∈ q := fun q hq hqp ↦
    Finset.inf_le (f := id) (Finset.mem_erase.2 ⟨hqp, hfin.mem_toFinset.2 hq⟩) hsF
  have hU : ¬ ((p : Set A) ⊆ ⋃ q ∈ minimalPrimes A \ {p}, ((fun q : Ideal A ↦ q) q : Set A)) := by
    rw [Ideal.subset_union_prime_finite (hfin.subset Set.sdiff_subset) p p (fun q hq _ _ ↦ hq.1.1.1)]
    rintro ⟨q, hq, hpq⟩
    exact hq.2 (eq_of_le_of_mem_minimalPrimes hp hq.1 hpq).symm
  obtain ⟨t, htp, htU⟩ := Set.not_subset.1 hU
  refine ⟨s, t, htp, hsp, fun q hq hqp ↦ ⟨hsq q hq hqp, fun htq ↦ htU ?_⟩⟩
  exact Set.mem_biUnion (⟨hq, hqp⟩ : q ∈ minimalPrimes A \ {p}) htq
end GroundTheory.Heights₂.Heights.MinimalPrimePlace
