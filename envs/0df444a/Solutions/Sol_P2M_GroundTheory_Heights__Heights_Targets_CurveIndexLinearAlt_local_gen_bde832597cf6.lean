-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_local_gen_bde832597cf6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:34:33.797035+00:00
-- url     : https://prove2.me/submissions/1e90eee1-ea32-4fe8-b68a-1b8f1db4a828

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_ne_zero_a60dcb0d33ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_div_e53e99228c31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_ne_zero_4ffc22541bb7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_secIdeal_9ac050eb4a81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_zpow_mem_of_9a48d073fbd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartRingZ_le_loc_4f0655af7099
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_uniform_denom_9c3df70fe533
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
theorem _root_.solution {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {m : Ideal (curveRing y)}
    (hm : m.IsPrime) {c' : ∀ k, ι k} (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0)
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c' p.1⟩) = α) (a : K → ℤ) :
    (∃ b : curveRing y, b ∉ m ∧ (b : Ω) * gen y c a c' ∈ secIdeal y c a) ∧
      ∀ z ∈ secIdeal y c a, ∃ b e : curveRing y, b ∉ m ∧ (b : Ω) * z = e * gen y c a c' := by
  have hg := gen_ne_zero hc hc' a
  refine ⟨?_, fun z hz => ?_⟩
  · have hloc : ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) →
        ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * (cu y c' a / cu y c'' a) ∈ chartRingZ y c'' := by
      intro c'' hc''
      have hS : ∀ b : curveRing y, (b : Ω) ∈ (chartRingZ y c'').toSubring := fun b => mem_curveRing.mp b.2 c'' hc''
      let T := locRing m hm (chartRingZ y c'').toSubring hS
      have hT : cu y c' a / cu y c'' a ∈ T := by
        rw [cu_div]
        refine prod_mem fun k _ => zpow_mem_of ?_ ?_ _
        · refine ⟨1, fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h), ?_⟩
          rw [OneMemClass.coe_one, one_mul]
          exact Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩
        · obtain ⟨α, β, hβ, e⟩ := hr ⟨k, c'' k⟩
          refine ⟨β, hβ, ?_⟩
          rw [inv_div, e]
          exact hS α
      exact hT
    obtain ⟨b, hb, hb'⟩ := uniform_denom hm _ hloc
    refine ⟨b, hb, (mem_secIdeal hc).mpr fun c'' hc'' => ?_⟩
    have hu'' := cu_ne_zero hc'' a
    have hu := cu_ne_zero hc a
    convert hb' c'' hc'' using 1
    simp only [gen]
    field_simp
  · have h1 := (mem_secIdeal hc).mp hz c' hc'
    obtain ⟨b, hb, hb'⟩ := chartRingZ_le_loc hm hr h1
    refine ⟨b, ⟨_, hb'⟩, hb, ?_⟩
    simp only
    field_simp
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
