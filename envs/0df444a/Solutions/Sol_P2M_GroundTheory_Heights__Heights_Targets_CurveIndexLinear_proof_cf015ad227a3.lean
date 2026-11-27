-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinear_proof_cf015ad227a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:20:08.7143+00:00
-- url     : https://prove2.me/submissions/d98da682-9361-4680-933c-cfa501746500

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinear_add_e19dd014d806

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
namespace GroundTheory.Heights₂.Heights.Targets
namespace CurveIndexLinear
theorem _root_.solution (hF : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement)
    (hI : InvertibleIndexMul.Statement) : CurveIndexLinear.Statement := by
  intro K _ ι _ Ω _ y c hP hc
  have hadd := CurveIndexLinear.add hF hC hI hP hc
  refine ⟨hadd, fun a τ => ?_⟩
  have hτ : chartIndexLog y c a τ = chartIndexLog y c (fun k => (τ : ℤ) * a k) 1 := by
    have e1 : chartLat y a τ = chartLat y (fun k => (τ : ℤ) * a k) 1 := by
      ext s
      show (∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
          s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingZ y c') ↔
        (∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
          s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * ((τ : ℤ) * a k))) ∈ chartRingZ y c')
      simp only [Nat.cast_one, one_mul]
    have e2 : chartUnit y c a τ = chartUnit y c (fun k => (τ : ℤ) * a k) 1 := by
      simp [chartUnit]
    rw [chartIndexLog, chartIndexLog, e1, e2]
  rw [hτ]
  clear hτ
  induction τ with
  | zero =>
    have h0 := hadd 0 0
    rw [add_zero] at h0
    have e : (fun k => ((0 : ℕ) : ℤ) * a k) = 0 := funext fun k => by simp
    rw [e]
    push_cast
    linarith
  | succ n ih =>
    have e : (fun k => ((n + 1 : ℕ) : ℤ) * a k) = (fun k => (n : ℤ) * a k) + a :=
      funext fun k => by simp only [Pi.add_apply]; push_cast; ring
    rw [e, hadd, ih]
    push_cast
    ring
end CurveIndexLinear
end GroundTheory.Heights₂.Heights.Targets
