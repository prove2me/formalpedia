-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_valuationSubring_0f9f3f936455
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:52.706648+00:00
-- url     : https://prove2.me/submissions/04f083de-2eaa-4165-b8c3-7b7b4cabe609

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointOfAlgebraicDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
variable {K : Type*} [Field K] {S : Type*} [CommRing S]
  [Algebra S K] [IsFractionRing S K] (M : Ideal S) [M.IsMaximal]
namespace GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
theorem _root_.solution :
    ∃ B : ValuationSubring K, (∀ s : S, algebraMap S K s ∈ B) ∧
      ∀ s ∈ M, B.valuation (algebraMap S K s) < 1 := by
  let e : S →+* (algebraMap S K).range := (algebraMap S K).rangeRestrict
  have he : Function.Bijective e :=
    ⟨fun a b h ↦ IsFractionRing.injective S K (congrArg Subtype.val h),
      (algebraMap S K).rangeRestrict_surjective⟩
  have hI : M.map e ≠ ⊤ := by
    intro h
    have h' := congrArg (Ideal.comap e) h
    rw [Ideal.comap_map_of_bijective e he, Ideal.comap_top] at h'
    exact (‹M.IsMaximal›).ne_top h'
  obtain ⟨B, hAB, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (M.map e) hI
  refine ⟨B, fun s ↦ hAB (RingHom.mem_range.2 ⟨s, rfl⟩), fun s hs ↦ ?_⟩
  rw [← ValuationSubring.mem_nonunits_iff]
  exact hB ⟨e s, Ideal.mem_map_of_mem e hs, rfl⟩
end GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
