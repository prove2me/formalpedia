-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNmSection_proof_21d0e7e6fb98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:30.971286+00:00
-- url     : https://prove2.me/submissions/a3d8f5b5-4e8f-4df8-a8b2-1127abc74709

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_isLive_iff__2b823a4f59be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_isIntegral_theta_iff_fe641e3ebc90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_reads_readElt_97ddeb3ac6cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_readElt_div_2c67889bc5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_isOfDegree_readElt_1d0629766c62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open ChartLatNm
namespace GroundTheory.Heights₂.Heights
namespace ChartLatNmSection
theorem _root_.solution : ChartLatNmSection.Statement := by
  intro ι _ _ n Ω _ y P a τ s hP hb
  obtain ⟨c₀, hc₀⟩ := P.exists_chart
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := (isLive_iff' P y hP c₀).mp hc₀
  have hab : ∀ k, -((τ : ℤ) * a k) = -((τ • a) k) := fun k => by simp
  have hmem : s ∈ Geo.chartLatNm (ι := blockIdx n) y a τ ↔
      ∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) →
        IsIntegral (Geo.chartRingZ (ι := blockIdx n) y c) (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ • a) k))) := by
    change (∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ integralClosure (Geo.chartRingZ (ι := blockIdx n) y c) Ω) ↔ _
    simp only [hab, mem_integralClosure_iff]
  rw [hmem]
  constructor
  · intro hs
    refine ⟨readElt P y hP hb c₀ (τ • a) s,
      ⟨isOfDegree_readElt P y hP hb c₀ hy₀ _ s, fun c hc => ?_⟩, reads_readElt P y hP hb c₀ hy₀ _ s⟩
    have hyc := (isLive_iff' P y hP c).mp hc
    rw [readElt_div P y hP hb c₀ c hy₀ hyc, mem_integralClosure_iff, isIntegral_theta_iff P y hP hb c hyc]
    exact hs c hyc
  · rintro ⟨t, ⟨hdeg, hint⟩, hR⟩ c hyc
    have hc := (isLive_iff' P y hP c).mpr hyc
    obtain ⟨f, q, δf, δq, hf, hq, hd, hqP, rfl⟩ := hdeg
    have hQ : P.mkF q ≠ 0 := fun h => hqP ((P.mkF_eq_zero_iff q).mp h)
    have hd' : ∀ k, (δf k : ℤ) = δq k + (τ • a) k := fun k => by linarith [hd k]
    have he := (hR f q δf δq hf hq hd').mpr (div_mul_cancel₀ _ hQ).symm
    have hmk := (reads_readElt P y hP hb c₀ hy₀ (τ • a) s f q δf δq hf hq hd').mp he
    have ht : P.mkF f / P.mkF q = readElt P y hP hb c₀ (τ • a) s := by
      rw [hmk, mul_div_cancel_right₀ _ hQ]
    have hi := hint c hc
    rw [ht, readElt_div P y hP hb c₀ c hy₀ hyc, mem_integralClosure_iff,
      isIntegral_theta_iff P y hP hb c hyc] at hi
    exact hi
end ChartLatNmSection
end GroundTheory.Heights₂.Heights
