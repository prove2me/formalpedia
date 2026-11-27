-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSection_proof_81c6478924ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:01:04.729923+00:00
-- url     : https://prove2.me/submissions/6035e4b8-2a2e-463d-8f11-c5fb213383dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_unit_all_01d1868a230d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_forall_prime_ca2e131ff074
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_centre_ac2831e01219
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_finite_centres_5a68fbf492f8

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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ClosedPointUnitSection
theorem _root_.solution : ClosedPointUnitSection.Statement := by
  intro T _ K' _ _ y hy m hm
  classical
  have hF := ClosedPointUnitSectionAlt.finite_centres y m hm
  obtain ⟨d, G, hd, hG0, hG, hGS⟩ := ClosedPointUnitSectionAlt.exists_unit_all y hy hF.toFinset
  refine ⟨d, G, hd, hG0, hG, fun W _ hunit u => ?_⟩
  by_cases hq : ∃ q : ℕ, q.Prime ∧ W.valuation (q : K') < 1
  · obtain ⟨q, hq, hWq⟩ := hq
    have hqm : (q : curveRing y) ∈ m := by
      by_contra h
      have := hunit _ h
      push_cast at this
      exact absurd this (ne_of_lt hWq)
    obtain ⟨P, hqP, hPW⟩ := ClosedPointUnitSectionAlt.exists_centre W hq hWq
    apply hPW
    have hPu := hGS P (hF.mem_toFinset.mpr ⟨q, hq, hqm, hqP⟩)
    rw [map_div₀]
    refine (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hG0))).mpr ?_
    rw [map_pow]
    exact hPu u
  · push Not at hq
    refine ClosedPointUnitSectionAlt.mem_of_forall_prime W (fun q hq' => le_antisymm ?_ (hq q hq')) _
    exact (W.valuation_le_one_iff _).mpr (natCast_mem W q)
end ClosedPointUnitSection
end GroundTheory.Heights₂.Heights
