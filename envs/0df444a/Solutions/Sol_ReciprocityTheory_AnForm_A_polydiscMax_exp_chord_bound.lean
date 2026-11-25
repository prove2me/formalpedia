-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.polydiscMax_exp_chord_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:31.776271+00:00
-- url     : https://prove2.me/submissions/bfc21ee2-3bd2-45d3-9b86-4ddf694adef8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_attained
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_exp_usc
import Theorems.Thm_ReciprocityTheory_AnForm_A_ca_const_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_ca_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hU : IsOpen U) (hφ : IsPsh U φ) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall z R ⊆ U) {a b α β : ℝ} (hab : a < b) (hb : b ≤ Real.log R)
    (ha' : polyMax φ z (Real.exp a) ≤ α + β * a) (hb' : polyMax φ z (Real.exp b) ≤ α + β * b)
    {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ∈ Icc a b) :
    polyMax φ z (Real.exp s) + δ * Real.exp s ^ 2 ≤ α + β * s + δ * Real.exp b ^ 2 := by
  set f : ℝ → ℝ := fun s => polyMax φ z (Real.exp s) with hf
  set H : ℝ → ℝ := fun s => f s + δ * Real.exp s ^ 2 - α - β * s - δ * Real.exp b ^ 2 with hH
  have hbR : Real.exp b ≤ R := (Real.exp_le_exp.2 hb).trans_eq (Real.exp_log hR0)
  have hfu : UpperSemicontinuousOn f (Icc a b) :=
    (polyMax_exp_usc hU hφ.1 hR0 hR).mono (fun x hx => hx.2.trans hb)
  have hHu : UpperSemicontinuousOn H (Icc a b) := by
    have hc : Continuous fun s : ℝ => δ * Real.exp s ^ 2 - α - β * s - δ * Real.exp b ^ 2 := by
      fun_prop
    have hHeq : H = fun x => f x + (δ * Real.exp x ^ 2 - α - β * x - δ * Real.exp b ^ 2) := by
      funext x
      show f x + δ * Real.exp x ^ 2 - α - β * x - δ * Real.exp b ^ 2 = _
      ring
    rw [hHeq]
    exact hfu.add (hc.upperSemicontinuous.upperSemicontinuousOn _)
  obtain ⟨s0, hs0, hmax⟩ := hHu.exists_isMaxOn ⟨a, left_mem_Icc.2 hab.le⟩ isCompact_Icc
  have hHs := isMaxOn_iff.1 hmax s hs
  suffices hneg : H s0 ≤ 0 by
    have : H s ≤ 0 := hHs.trans hneg
    simp only [hH, hf] at this
    linarith
  by_contra hpos
  push Not at hpos
  have hea : Real.exp a ^ 2 ≤ Real.exp b ^ 2 := by
    have := Real.exp_le_exp.2 hab.le
    have := Real.exp_pos a
    nlinarith
  have ha0 : a < s0 := by
    rcases eq_or_lt_of_le hs0.1 with h | h
    · rw [← h] at hpos
      simp only [hH, hf] at hpos
      nlinarith
    · exact h
  have hs0b : s0 < b := by
    rcases eq_or_lt_of_le hs0.2 with h | h
    · rw [h] at hpos
      simp only [hH, hf] at hpos
      nlinarith
    · exact h
  set r0 := Real.exp s0 with hr0
  have hr0pos : 0 < r0 := Real.exp_pos _
  have h1 : Real.exp a < r0 := Real.exp_lt_exp.2 ha0
  have h2 : r0 < Real.exp b := Real.exp_lt_exp.2 hs0b
  set ρ := min (r0 - Real.exp a) (Real.exp b - r0) with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρ1 : ρ ≤ r0 - Real.exp a := min_le_left _ _
  have hρ2 : ρ ≤ Real.exp b - r0 := min_le_right _ _
  have hea0 : 0 < Real.exp a := Real.exp_pos a
  have hr0U : closedBall z r0 ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hR
  obtain ⟨x0, hx0, hx0e⟩ := polyMax_attained hφ.1 hr0pos.le hr0U
  set u0 : Fin D → ℂ := ((r0 : ℂ)⁻¹) • (x0 - z) with hu0def
  have hr0c : (r0 : ℂ) ≠ 0 := by exact_mod_cast hr0pos.ne'
  have hu0 : ‖u0‖ ≤ 1 := by
    rw [mem_closedBall, dist_eq_norm] at hx0
    calc ‖u0‖ = r0⁻¹ * ‖x0 - z‖ := by
          simp [u0, norm_smul, abs_of_pos hr0pos]
      _ ≤ r0⁻¹ * r0 := by gcongr
      _ = 1 := inv_mul_cancel₀ hr0pos.ne'
  have hx0eq : x0 = z + (r0 : ℂ) • u0 := by
    rw [hu0def, smul_smul, mul_inv_cancel₀ hr0c, one_smul, add_sub_cancel]
  clear_value u0
  set P : ℂ → ℂ := fun ζ => (r0 : ℂ) + (ρ : ℂ) * ζ with hP
  have hPle : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖P ζ‖ ≤ r0 + ρ := by
    intro ζ hζ
    calc ‖P ζ‖ ≤ ‖(r0 : ℂ)‖ + ‖(ρ : ℂ) * ζ‖ := norm_add_le _ _
      _ = r0 + ρ * ‖ζ‖ := by simp [abs_of_pos hr0pos, abs_of_pos hρpos]
      _ ≤ r0 + ρ := by nlinarith [norm_nonneg ζ]
  have hPge : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → r0 - ρ ≤ ‖P ζ‖ := by
    intro ζ hζ
    have := norm_sub_le (P ζ) ((ρ : ℂ) * ζ)
    have e : P ζ - (ρ : ℂ) * ζ = r0 := by simp [P]
    rw [e] at this
    have : ‖(r0 : ℂ)‖ = r0 := by simp [abs_of_pos hr0pos]
    have : ‖(ρ : ℂ) * ζ‖ = ρ * ‖ζ‖ := by simp [abs_of_pos hρpos]
    nlinarith [norm_nonneg ζ]
  have hPpos : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → 0 < ‖P ζ‖ := fun ζ hζ => by linarith [hPge ζ hζ]
  set w : Fin D → ℂ := (ρ : ℂ) • u0 with hw
  have hpt : ∀ ζ : ℂ, x0 + ζ • w = z + P ζ • u0 := by
    intro ζ
    rw [hx0eq, hw, smul_smul, add_assoc, ← add_smul]
    congr 2
    simp only [P]
    ring
  have hin : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → x0 + ζ • w ∈ closedBall z ‖P ζ‖ := by
    intro ζ hζ
    rw [hpt, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg (P ζ)]
  have hballU : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → closedBall z ‖P ζ‖ ⊆ U := fun ζ hζ =>
    (closedBall_subset_closedBall (by linarith [hPle ζ hζ])).trans hR
  obtain ⟨hint, hmean⟩ := hφ.2 x0 w (fun ζ hζ => hballU ζ hζ (hin ζ hζ))

  set K := H s0 + α + δ * Real.exp b ^ 2 with hK
  set g : ℂ → ℝ := fun ζ => K - δ * ‖P ζ‖ ^ 2 + β * Real.log ‖P ζ‖ with hg
  have hbound : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → φ (x0 + ζ • w) ≤ g ζ := by
    intro ζ hζ
    have hpos := hPpos ζ hζ
    have hX : Real.log ‖P ζ‖ ∈ Icc a b := by
      constructor
      · rw [Real.le_log_iff_exp_le hpos]; linarith [hPge ζ hζ]
      · rw [Real.log_le_iff_le_exp hpos]; linarith [hPle ζ hζ]
    have hHX := isMaxOn_iff.1 hmax _ hX
    simp only [hH, hf, Real.exp_log hpos] at hHX
    have := le_polyMax hφ.1 (hballU ζ hζ) (hin ζ hζ)
    simp only [hg, hK]
    linarith
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) |1|, ‖ζ‖ = 1 := by intro ζ hζ; simpa using hζ
  have hcb : ∀ ζ ∈ closedBall (0 : ℂ) |1|, ‖ζ‖ ≤ 1 := by intro ζ hζ; simpa using hζ
  have hPd : Differentiable ℂ P := by rw [hP]; fun_prop
  have hPcont : Continuous P := hPd.continuous
  have hlogc : ContinuousOn (fun ζ => Real.log ‖P ζ‖) (sphere (0 : ℂ) |1|) :=
    (hPcont.norm.continuousOn).log (fun ζ hζ => (hPpos ζ (hsph ζ hζ).le).ne')
  have hsqc : Continuous (fun ζ => ‖P ζ‖ ^ 2) := hPcont.norm.pow 2
  have hA2 : Real.circleAverage (fun ζ => Real.log ‖P ζ‖) 0 1 = s0 := by
    have han : AnalyticOnNhd ℂ P (closedBall 0 |1|) := fun x _ => hPd.analyticAt x
    rw [AnalyticOnNhd.circleAverage_log_norm_of_ne_zero han
      (fun u hu => norm_ne_zero_iff.1 (hPpos u (hcb u hu)).ne')]
    have : P 0 = (r0 : ℂ) := by simp [hP]
    rw [this, Complex.norm_real, Real.norm_of_nonneg hr0pos.le, hr0, Real.log_exp]
  have hA1 : Real.circleAverage (fun ζ => ‖P ζ‖ ^ 2) 0 1 = r0 ^ 2 + ρ ^ 2 := by
    have heq : Set.EqOn (fun ζ => ‖P ζ‖ ^ 2) (fun ζ => (r0 ^ 2 + ρ ^ 2) + (2 * r0 * ρ) * ζ.re)
        (sphere (0 : ℂ) |1|) := by
      intro ζ hζ
      have hn := hsph ζ hζ
      have h1 : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
        rw [← Complex.normSq_apply, ← Complex.sq_norm, hn]; norm_num
      simp only [hP]
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      linear_combination ρ ^ 2 * h1
    rw [Real.circleAverage_congr_sphere heq, Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
      ((by fun_prop : Continuous (fun ζ : ℂ => 2 * r0 * ρ * ζ.re)).continuousOn.circleIntegrable'),
      Real.circleAverage_const, ca_const_mul, ca_re]
    ring
  have hgint : CircleIntegrable g 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact (continuousOn_const.sub (continuousOn_const.mul hsqc.continuousOn)).add
      (continuousOn_const.mul hlogc)
  have hCAg : Real.circleAverage g 0 1 = K - δ * (r0 ^ 2 + ρ ^ 2) + β * s0 := by
    have i1 : CircleIntegrable (fun ζ => K - δ * ‖P ζ‖ ^ 2) 0 1 :=
      (continuous_const.sub (continuous_const.mul hsqc)).continuousOn.circleIntegrable'
    have i2 : CircleIntegrable (fun ζ => β * Real.log ‖P ζ‖) 0 1 :=
      (continuousOn_const.mul hlogc).circleIntegrable'
    have i3 : CircleIntegrable (fun ζ => δ * ‖P ζ‖ ^ 2) 0 1 :=
      (continuous_const.mul hsqc).continuousOn.circleIntegrable'
    rw [hg, Real.circleAverage_fun_add i1 i2, Real.circleAverage_fun_sub
      (circleIntegrable_const _ _ _) i3,
      Real.circleAverage_const, ca_const_mul, ca_const_mul, hA1, hA2]
  have hφx0 : φ x0 = H s0 - δ * r0 ^ 2 + α + β * s0 + δ * Real.exp b ^ 2 := by
    rw [hx0e]
    show polyMax φ z r0 = (polyMax φ z r0 + δ * r0 ^ 2 - α - β * s0 - δ * Real.exp b ^ 2)
      - δ * r0 ^ 2 + α + β * s0 + δ * Real.exp b ^ 2
    ring
  have hle := hmean.trans
    (Real.circleAverage_mono hint hgint (fun ζ hζ => hbound ζ (hsph ζ hζ).le))
  rw [hCAg, hφx0] at hle
  linarith [hK, mul_pos hδ (pow_pos hρpos 2)]
end ReciprocityTheory.AnForm.A
