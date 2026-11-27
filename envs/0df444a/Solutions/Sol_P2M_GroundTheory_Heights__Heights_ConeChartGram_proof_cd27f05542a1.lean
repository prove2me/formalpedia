-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeChartGram_proof_cd27f05542a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:34.372602+00:00
-- url     : https://prove2.me/submissions/29435962-eb08-4550-b2d1-80ff7572bee2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeChartGram
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_bounded_of_degree_zero_dbafb3416947
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_of_ringKrullDim_quotient_ba1fbfb39ad7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneBall_hausdorff_lt_top_a8bd40dcd9c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_line_gram_cd685deb188c
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeChartGram
theorem _root_.solution (hArea : ConeSheetGram.Statement) (hMF : MassFinite.Statement) :
    ConeChartGram.Statement := by
  intro n e h J ℓ g A hJ hdim hℓ hdeg hcont hA
  set f : EuclideanSpace ℂ (Fin n) → ℝ :=
    (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z)) with hf
  have hset : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} =
      {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} ∩ ball 0 1 := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]
    exact and_comm
  have hgm : Measurable g := measurable_of_continuousOn_compl_singleton 0 (hcont.mono fun x hx => hx)
  have hpm : Continuous fun z : EuclideanSpace ℂ (Fin n) => h.pointOf z := by
    unfold HermNorm.pointOf
    exact continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _)
  obtain ⟨B, hB⟩ := bounded_of_degree_zero g hdeg hcont
  have hfin := coneBall_hausdorff_lt_top hMF h J hJ.isPrime hdim
  have hint : IntegrableOn f {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}
      (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [IntegrableOn, hf, integrable_indicator_iff measurableSet_ball, IntegrableOn,
      Measure.restrict_restrict measurableSet_ball, inter_comm, ← hset]
    have : IsFiniteMeasure ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict
        {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0}) :=
      isFiniteMeasure_restrict.2 hfin.ne
    exact Integrable.of_bound (hgm.comp hpm.measurable).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB _)
  have key := hArea n e h J ℓ A f hJ hdim hℓ hA hint
  have hterm : ∀ y : Fin e → ℂ, sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
      (fun _ s => ∫ t : ℂ, f (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y)) *
        (‖t‖ ^ (2 * e) * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y)) y =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) * sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
        (fun x s => g x * ((e.factorial : ℝ) / Real.pi ^ e *
          gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y / h.dualNorm x ^ (2 * (e + 1)))) y := by
    intro y
    unfold sheetSum
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun x hx => ?_
    split_ifs with hs
    · obtain ⟨-, -, -, -, hsx, -⟩ := hs.choose_spec
      have hy : hs.choose y = x := by rw [← hx.2]; exact hsx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have hmem := hx.1 (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        simp [linForm] at hmem
      beta_reduce
      rw [hy]
      exact integral_line_gram e h g hdeg x hx0 _
    · simp
  simp_rw [hterm, integral_const_mul] at key
  obtain ⟨hM0, hMtop⟩ := coordBall_mass (n := n) (m := e + 1) (le_of_ringKrullDim_quotient J hdim)
  have hM : 0 < (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → z j = 0}).toReal :=
    ENNReal.toReal_pos hM0.ne' hMtop.ne
  have hc : (0 : ℝ) < Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) := by positivity
  have hleft : ∫ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, f z
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫ z in {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0},
        g (h.pointOf z) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [hf, setIntegral_indicator measurableSet_ball, hset]
  rw [hleft] at key
  unfold coneIntegral
  rw [div_eq_iff hM.ne']
  rw [mul_left_comm] at key
  rw [mul_left_cancel₀ hc.ne' key, mul_comm]
end ConeChartGram
end GroundTheory.Heights₂.Heights
