-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeChartArea_proof_7d0f995af667
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:42:54.270314+00:00
-- url     : https://prove2.me/submissions/d5f99e51-8918-41e5-877e-df5624c8e2ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_of_isArithVar_pblk_fb6970ea00bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_chosenSheet_eq_6c401d343d67
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)
namespace GroundTheory.Heights₂.Heights
namespace ConeChartArea
theorem _root_.solution (hA : ConeSheetArea.Statement) : ConeChartArea.Statement := by
  intro n e S hS P Ψ g hP hΨ _hgm hdeg hint
  set C := coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) with hC
  set f : EuclideanSpace ℂ (Fin n) → ℝ := (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
    (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y)) with hf
  have hset : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ complexFibreIdeal P,
      eval ((ObjectsHeight.ofPointMatrix S hS).pointOf y) q = 0} = C ∩ ball 0 1 := by
    ext y
    simp only [hC, coneSet, mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]
    exact and_comm
  have hfC : IntegrableOn f C (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [IntegrableOn, hf, integrable_indicator_iff measurableSet_ball, IntegrableOn,
      Measure.restrict_restrict measurableSet_ball, inter_comm]
    rw [hset] at hint
    exact hint
  have key := hA n e S hS P Ψ f hP hΨ hfC
  have hterm : ∀ x : Fin e → ℂ, (∑ᶠ w ∈ fibre P Ψ x, ∫ t : ℂ,
      f (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        (‖t‖ ^ (2 * e) * gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        ∑ᶠ w ∈ fibre P Ψ x, chartGramDensity P Ψ S g x w := by
    intro x
    rw [mul_finsum_mem]
    exact finsum_mem_congr rfl fun w _ => integral_chosenSheet_eq S hS P Ψ g hdeg x w
  simp_rw [hterm, integral_const_mul] at key
  obtain ⟨hM0, hMtop⟩ := coordBall_mass (n := n) (m := e + 1) (le_of_isArithVar_pblk hP)
  have hM : 0 < (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal :=
    ENNReal.toReal_pos hM0.ne' hMtop.ne
  have hc : (0 : ℝ) < Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) := by positivity
  have hleft : ∫ y in C, f y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫ y in {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ complexFibreIdeal P,
        eval ((ObjectsHeight.ofPointMatrix S hS).pointOf y) q = 0},
        g ((ObjectsHeight.ofPointMatrix S hS).pointOf y)
          ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [hf, setIntegral_indicator measurableSet_ball, hset]
  rw [hleft] at key
  unfold coneIntegral
  rw [div_eq_iff hM.ne']
  have key' := key
  rw [mul_left_comm] at key'
  have := mul_left_cancel₀ hc.ne' key'
  rw [this, mul_comm]
end ConeChartArea
end GroundTheory.Heights₂.Heights
