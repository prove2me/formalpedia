-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_chartLat_one_d525f1fe8df3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:36.826702+00:00
-- url     : https://prove2.me/submissions/58f4688a-fa6a-46c2-9542-cbf4d8fe4b89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear

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
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
theorem _root_.solution {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} :
    s ∈ chartLat y a 1 ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s / cu y c a ∈ chartRingZ y c := by
  have e : ∀ c : ∀ k, ι k, ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) = (cu y c a)⁻¹ := by
    intro c
    simp [cu, zpow_neg, Finset.prod_inv_distrib]
  show (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ chartRingZ y c) ↔ _
  simp only [e, div_eq_mul_inv]
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
