-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_chartIdeal_eq_ker_7be0f566e7f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:12:59.1459+00:00
-- url     : https://prove2.me/submissions/8e975dd4-9152-4ed9-8488-d2182a57182e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_mul_of_isMultiHomog_e86f9b353a4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_exists_homog_congr_b695ff76f041


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k)
variable {z j}
namespace GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
theorem _root_.solution [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0)
    (hP : IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ'))) :
    chartIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
  have hprod : ∀ a : K → ℕ, ∏ k, z ⟨k, j k⟩ ^ a k ≠ 0 :=
    fun a => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  have hunit : Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver Φ ι) - 1) ≤
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, affCoord]
    rw [div_self (hz k), sub_self]
  refine le_antisymm (sup_le ?_ hunit) fun f hf => ?_
  · obtain ⟨S, hS, hPS⟩ := hP
    rw [hPS, Ideal.span_le]
    intro s hs
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [hPS]; exact Ideal.subset_span hs
    have h1 := aeval_mul_of_isMultiHomog hz ha
    rw [RingHom.mem_ker.mp hsP] at h1
    exact RingHom.mem_ker.mpr ((mul_eq_zero.mp h1).resolve_right (hprod a))
  · obtain ⟨N, hN⟩ := NumbersDVR.IntNumPoint.exists_homog_congr j f
    obtain ⟨h, hh, hc⟩ := hN N le_rfl
    have hfh : f - h ∈ NumbersDVR.IntNumPoint.chartUnitIdeal (F := Φ) j := Ideal.Quotient.eq.mp hc
    have h0 : aeval (affCoord z j) h = 0 := by
      have := RingHom.mem_ker.mp (hunit hfh)
      rwa [map_sub, RingHom.mem_ker.mp hf, zero_sub, neg_eq_zero] at this
    have hhP : h ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [RingHom.mem_ker, ← aeval_mul_of_isMultiHomog hz ((Bridge.isMultiHomog_iff h N).mp hh), h0,
        zero_mul]
    have : f = (f - h) + h := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hhP)
end GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
