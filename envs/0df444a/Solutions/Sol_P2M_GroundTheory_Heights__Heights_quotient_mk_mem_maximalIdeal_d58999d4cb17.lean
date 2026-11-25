-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_quotient_mk_mem_maximalIdeal_d58999d4cb17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:31.344092+00:00
-- url     : https://prove2.me/submissions/7bafebde-941a-48d0-8490-f627236225a7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMProjDimCriterion

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
open IsLocalRing CategoryTheory RingTheory.Sequence
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] (hJ : J ≤ maximalIdeal S) {r : S} (hr : r ∈ maximalIdeal S) :
    Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  have h1 : r * s - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, map_one, sub_self]
  have h2 : (1 : S) ∈ maximalIdeal S := by
    have := sub_mem ((maximalIdeal S).mul_mem_right s hr) (hJ h1)
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
end GroundTheory.Heights₂.Heights
