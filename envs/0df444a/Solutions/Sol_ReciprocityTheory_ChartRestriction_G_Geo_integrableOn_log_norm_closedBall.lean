-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.integrableOn_log_norm_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:17:29.571709+00:00
-- url     : https://prove2.me/submissions/be6cf1ee-2e18-4a37-9ae3-e9d06bde2e21

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isPsh_logmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_subMeanPolydisc_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology Real
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {f : (Fin D → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U) {z0 : Fin D → ℂ} {t : ℝ} (ht : 0 < t)
    (hS2 : ball z0 (2 * t) ⊆ U) (hz0 : f z0 ≠ 0) :
    IntegrableOn (fun z => Real.log ‖f z‖) (closedBall z0 t) := by
  set B := closedBall z0 t with hBdef
  have hBU : B ⊆ U := fun x hx =>
    hS2 (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (by linarith)))
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBfin : volume B < ⊤ := measure_closedBall_lt_top
  have hfc : ContinuousOn f B := hf.continuousOn.mono hBU
  set c : ℝ := min ‖f z0‖ 1 with hc
  have hc0 : 0 < c := lt_min (norm_pos_iff.2 hz0) one_pos
  set ε : ℕ → ℝ := fun n => c / ((n : ℝ) + 1) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => div_pos hc0 (by positivity)
  have hεc : ∀ n, ε n ≤ c := fun n =>
    div_le_self hc0.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hε1 : ∀ n, ε n ≤ 1 := fun n => (hεc n).trans (min_le_right _ _)
  have hεanti : ∀ m n : ℕ, m ≤ n → ε n ≤ ε m := fun m n hmn =>
    div_le_div_of_nonneg_left hc0.le (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hmn; linarith)
  set φ : ℕ → (Fin D → ℂ) → ℝ := fun n x => Real.log (max ‖f x‖ (ε n)) with hφdef
  set φ1 : (Fin D → ℂ) → ℝ := fun x => Real.log (max ‖f x‖ 1) with hφ1def
  have hsub : ∀ n, IntegrableOn (φ n) B ∧ φ n z0 ≤ ⨍ x in B, φ n x := fun n =>
    ReciprocityTheory.AnForm.A.subMeanPolydisc_thm D U (φ n) z0 t hU (isPsh_logmax hU hf (hε0 n)) ht hBU
  have hφc : ∀ n, ContinuousOn (φ n) B := fun n =>
    ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right (hε0 n)).ne')
  have hφ1c : ContinuousOn φ1 B :=
    ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne')
  have hφ1i : IntegrableOn φ1 B := ContinuousOn.integrableOn_compact (isCompact_closedBall z0 t) hφ1c
  have hφz0 : ∀ n, φ n z0 = Real.log ‖f z0‖ := fun n => by
    simp only [hφdef]
    rw [max_eq_left ((hεc n).trans (min_le_left _ _))]
  have hφle : ∀ n x, φ n x ≤ φ1 x := fun n x =>
    Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hε1 n))
  have hφanti : ∀ m n : ℕ, m ≤ n → ∀ x, φ n x ≤ φ m x := fun m n hmn x =>
    Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hεanti m n hmn))
  set V := (volume B).toReal with hVdef
  have hV : 0 < V := ENNReal.toReal_pos (measure_closedBall_pos volume z0 ht).ne' hBfin.ne
  have hlow : ∀ n, V * Real.log ‖f z0‖ ≤ ∫ x in B, φ n x := by
    intro n
    have h1 : Real.log ‖f z0‖ ≤ V⁻¹ * ∫ x in B, φ n x := by
      have h2 := (hsub n).2
      rw [setAverage_eq, smul_eq_mul] at h2
      exact (hφz0 n).symm.le.trans h2
    have h3 := mul_le_mul_of_nonneg_left h1 hV.le
    rwa [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul] at h3
  set G : (Fin D → ℂ) → ℝ := fun x => φ1 x - Real.log ‖f x‖ with hGdef
  have hG0 : ∀ x, 0 ≤ G x := by
    intro x
    simp only [hGdef, hφ1def, sub_nonneg]
    by_cases hx : f x = 0
    · simp [hx]
    · exact Real.log_le_log (norm_pos_iff.2 hx) (le_max_left _ _)
  have hpt : ∀ x, ENNReal.ofReal (G x) ≤ ⨆ n, ENNReal.ofReal (φ1 x - φ n x) := by
    intro x
    by_cases hx : f x = 0
    · have : G x = 0 := by simp [hGdef, hφ1def, hx]
      rw [this, ENNReal.ofReal_zero]; exact zero_le
    · have hpos : 0 < ‖f x‖ := norm_pos_iff.2 hx
      obtain ⟨n, hn⟩ := exists_nat_gt (c / ‖f x‖)
      have hn' : ε n ≤ ‖f x‖ := by
        rw [div_lt_iff₀ hpos] at hn
        show c / ((n : ℝ) + 1) ≤ ‖f x‖
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      refine le_iSup_of_le n (le_of_eq ?_)
      congr 1
      simp only [hGdef, hφdef, max_eq_left hn']
  have hmeasn : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ1 x - φ n x)) (volume.restrict B) :=
    fun n => ((hφ1c.sub (hφc n)).aemeasurable hBm).ennreal_ofReal
  have hsup : ∫⁻ x in B, ⨆ n, ENNReal.ofReal (φ1 x - φ n x) =
      ⨆ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) :=
    lintegral_iSup' hmeasn (Filter.Eventually.of_forall fun x m n hmn =>
      ENNReal.ofReal_le_ofReal (sub_le_sub_left (hφanti m n hmn x) _))
  have hbound : ∀ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) ≤
      ENNReal.ofReal ((∫ x in B, φ1 x) - V * Real.log ‖f z0‖) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => φ1 x - φ n x) (hφ1i.sub (hsub n).1)
      (Filter.Eventually.of_forall fun x => sub_nonneg.2 (hφle n x))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub hφ1i (hsub n).1]
    linarith [hlow n]
  have hfin : ∫⁻ x in B, ENNReal.ofReal (G x) < ⊤ :=
    lt_of_le_of_lt ((lintegral_mono hpt).trans (hsup.le.trans (iSup_le hbound))) ENNReal.ofReal_lt_top
  have hlogm : AEStronglyMeasurable (fun x => Real.log ‖f x‖) (volume.restrict B) :=
    (Real.measurable_log.comp_aemeasurable ((ContinuousOn.norm hfc).aemeasurable hBm)).aestronglyMeasurable
  have hGi : IntegrableOn G B :=
    ⟨(hφ1c.aestronglyMeasurable hBm).sub hlogm,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)).2 hfin⟩
  refine (hφ1i.sub hGi).congr_fun (fun x _ => ?_) hBm
  simp [hGdef]
end ReciprocityTheory.ChartRestriction.G.Geo
