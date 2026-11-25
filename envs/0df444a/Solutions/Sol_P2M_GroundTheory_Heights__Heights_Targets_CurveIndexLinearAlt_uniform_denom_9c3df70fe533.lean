-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_uniform_denom_9c3df70fe533
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:38.312354+00:00
-- url     : https://prove2.me/submissions/92bc01e2-06dd-432d-b215-ef673a67cbf9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
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
theorem _root_.solution {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} (hm : m.IsPrime) (r : (∀ k, ι k) → Ω)
    (h : ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) →
      ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * r c'' ∈ chartRingZ y c'') :
    ∃ b : curveRing y, b ∉ m ∧ ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) →
      (b : Ω) * r c'' ∈ chartRingZ y c'' := by
  classical
  choose f hf using h
  let F : (∀ k, ι k) → curveRing y := fun c'' => if h : (∀ k, y ⟨k, c'' k⟩ ≠ 0) then f c'' h else 1
  have hF : ∀ c'', F c'' ∈ m.primeCompl := by
    intro c''
    by_cases h : ∀ k, y ⟨k, c'' k⟩ ≠ 0
    · simp only [F, dif_pos h]; exact (hf c'' h).1
    · simp only [F, dif_neg h]; exact m.primeCompl.one_mem
  refine ⟨∏ c'', F c'', Submonoid.prod_mem _ fun c'' _ => hF c'', fun c'' hc'' => ?_⟩
  obtain ⟨q, hq⟩ : F c'' ∣ ∏ c, F c := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  rw [hq]
  have h2 : (F c'' : Ω) * r c'' ∈ chartRingZ y c'' := by simpa [F, dif_pos hc''] using (hf c'' hc'').2
  have h3 : (q : Ω) ∈ chartRingZ y c'' := mem_curveRing.mp q.2 c'' hc''
  have := (chartRingZ y c'').mul_mem h3 h2
  convert this using 1
  push_cast
  ring
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
