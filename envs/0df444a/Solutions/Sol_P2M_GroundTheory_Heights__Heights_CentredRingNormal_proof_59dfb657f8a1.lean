-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CentredRingNormal_proof_59dfb657f8a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:52:56.678618+00:00
-- url     : https://prove2.me/submissions/87ef5e08-6cd7-4ea3-b341-6e455ddb819e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_isIntegral_of_comp_3ac7131e96c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_mem_valuationSubring_iff_place_091f0caf95c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_exists_place_of_valuationSubring_ca02ac74434f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_absCentredAt_of_le_one_ebd98841079e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_placesRing_4624459aa66d


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
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]
namespace GroundTheory.Heights₂.Heights.CentredRingNormal
theorem _root_.solution : CentredRingNormal.Statement := by
  intro L _ _ O _ _ m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hcent : ∀ w : FinitePlace L, AbsCentredAt O m (fun t ↦ w t) → ∀ y ∈ A, w y ≤ 1 := by
    rintro w ⟨hO, hm⟩ y ⟨a, s, hs, rfl⟩
    have hs1 : w (algebraMap O L s) = 1 := le_antisymm (hO s) (not_lt.mp fun h ↦ hs ((hm s).mp h))
    rw [map_mul, map_inv₀, hs1, inv_one, mul_one]
    exact hO a
  ext x
  rw [mem_placesRing, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · intro hx
    have hall : x ∈ ⨅ V : {V : ValuationSubring L // (A : Set L) ⊆ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.mpr fun ⟨V, hAV⟩ ↦ ?_
      by_cases hV : V = ⊤
      · have h : x ∈ V := hV ▸ ValuationSubring.mem_top x
        exact h
      obtain ⟨w, hw⟩ := exists_place_of_valuationSubring V hV
      by_contra hxV
      have hwx : 1 < w x := not_le.mp fun h ↦ hxV ((hw x).mpr h)
      have hc := absCentredAt_of_le_one O m w (fun y hy ↦ (hw y).mp (hAV hy)) x hwx
      exact hxV ((hw x).mpr (hx w hc))
    rw [iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hall
    refine isIntegral_of_comp ((algebraMap (Subring.closure (A : Set L)) L).codRestrict A fun y ↦ ?_) (RingHom.ext fun _ ↦ rfl) hall
    exact (Subring.closure_le (t := A.toSubring)).mpr (fun z hz ↦ hz) y.2
  · intro hx w hw
    let v := FinitePlace.maximalIdeal w
    have hAV : ∀ y ∈ A, y ∈ (v.valuation L).valuationSubring := fun y hy ↦ by
      rw [mem_valuationSubring_iff_place, FinitePlace.mk_maximalIdeal]
      exact hcent w hw y hy
    have hxV : IsIntegral (v.valuation L).valuationSubring x :=
      isIntegral_of_comp ((algebraMap A L).codRestrict _ fun y ↦ hAV y y.2)
        (RingHom.ext fun _ ↦ rfl) hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxV
    have h := (mem_valuationSubring_iff_place v x).mp (hy ▸ y.2)
    rwa [FinitePlace.mk_maximalIdeal] at h
end GroundTheory.Heights₂.Heights.CentredRingNormal
