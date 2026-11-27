-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.levi_psD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:31.965672+00:00
-- url     : https://prove2.me/submissions/06a5256f-f3a9-4432-99a5-506a338ed213

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviV_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_contDiffAt_two_of_holo
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_aap_sqn_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_holo_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_ph_eq_sub_nsmul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffAt_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_log_sum_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_exp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution {N : ℕ} {L la : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (hPosL : A.Pos L fun _ => 0)
    {ps1 : Y → ℝ} (hps1 : A.SmoothFn ps1) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hLevi : ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      2 * η * A.leviAt i (A.ph L i) y ξ ≤
        A.leviAt i (fun x => A.ph (la - n • L) i x + ps1 x) y ξ)
    (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    η * A.leviAt i (A.ph L i) y ξ ≤
      A.leviAt i (fun x => A.ph la i x + A.psD L w s ps1 η δ x) y ξ := by
  set φ := A.chart i
  set v0 := φ y
  have hv0 : v0 ∈ φ.target := φ.map_source hy
  have hT : φ.target ∈ 𝓝 v0 := φ.open_target.mem_nhds hv0
  have hsy : φ.symm v0 = y := φ.left_inv hy
  set a : V n → ℝ := fun v => A.ph (la - n • L) i (φ.symm v) + ps1 (φ.symm v)
  set b : V n → ℝ := fun v => A.ph L i (φ.symm v)
  set W : V n → ℝ := fun v => ∑ k, Complex.normSq (w k i (φ.symm v))
  set Sv : V n → ℝ := fun v => Real.exp (b v + Real.log δ) + ∑ k, Complex.normSq (s k i (φ.symm v))
  have hwC : ∀ k, ContDiffAt ℂ 2 (w k i ∘ φ.symm) v0 := fun k =>
    contDiffAt_two_of_holo φ.open_target (A.holo_chart (hD.sec_w k) i) hv0
  have hsC : ∀ k, ContDiffAt ℂ 2 (s k i ∘ φ.symm) v0 := fun k =>
    contDiffAt_two_of_holo φ.open_target (A.holo_chart (hD.sec_s k) i) hv0
  have ha : ContDiffAt ℝ 2 a v0 :=
    (((A.smooth_ph (la - n • L) i).add (hps1 i)).contDiffAt hT).of_le (by norm_cast)
  have hb : ContDiffAt ℝ 2 b v0 := ((A.smooth_ph L i).contDiffAt hT).of_le (by norm_cast)
  have hW0 : 0 < W v0 := by
    have h := A.aap_sqn_pos hD y
    rw [A.sqn_chart L w hD.sec_w i hy] at h
    have h2 : 0 < ∑ k, ‖w k i y‖ ^ 2 := pos_of_mul_pos_left h (Real.exp_pos _).le
    simpa [W, hsy, Complex.normSq_eq_norm_sq] using h2
  have hS0 : 0 < Sv v0 := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (s k i (φ.symm v0))
    have := Real.exp_pos (b v0 + Real.log δ); simp only [Sv]; linarith
  have hWC : ContDiffAt ℝ 2 W v0 := ContDiffAt.sum fun k _ => contDiffAt_normSq_comp (hwC k)
  have hbd : ContDiffAt ℝ 2 (fun v => b v + Real.log δ) v0 := hb.add contDiffAt_const
  have hSC : ContDiffAt ℝ 2 Sv v0 :=
    (Real.contDiff_exp.contDiffAt.comp v0 hbd).add
      (ContDiffAt.sum fun k _ => contDiffAt_normSq_comp (hsC k))
  have hlW : ContDiffAt ℝ 2 (fun v => Real.log (W v)) v0 := hWC.log hW0.ne'
  have hlS : ContDiffAt ℝ 2 (fun v => Real.log (Sv v)) v0 := hSC.log hS0.ne'

  have hLW : 0 ≤ (leviV n (fun v => ((Real.log (W v) : ℝ) : ℂ)) v0 ξ).re :=
    leviV_log_sum_nonneg (u := fun k v => Complex.normSq (w k i (φ.symm v)))
      (fun k => contDiffAt_normSq_comp (hwC k)) (fun k => logPshAt_normSq (hwC k)) hW0 ξ
  have hPb : ∀ ζ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((b v + Real.log δ : ℝ) : ℂ)) v0 ζ).re := by
    intro ζ
    have h1 : (fun v => ((b v + Real.log δ : ℝ) : ℂ)) = fun v => ((1 * b v + Real.log δ : ℝ) : ℂ) := by
      simp
    rw [h1, leviV_const_mul hb, Complex.ofReal_one, one_mul]
    have h2 := hPosL i y hy ζ
    simpa [leviAt] using h2
  have hLS : 0 ≤ (leviV n (fun v => ((Real.log (Sv v) : ℝ) : ℂ)) v0 ξ).re := by
    set u : Fin (n + 1) → V n → ℝ :=
      Fin.cons (fun v => Real.exp (b v + Real.log δ)) (fun k v => Complex.normSq (s k i (φ.symm v)))
    have hsum : (fun v => ((Real.log (Sv v) : ℝ) : ℂ)) = fun v => ((Real.log (∑ j, u j v) : ℝ) : ℂ) := by
      funext v; simp [u, Sv, Fin.sum_univ_succ]
    rw [hsum]
    refine leviV_log_sum_nonneg (fun j => ?_) (fun j => ?_) ?_ ξ
    · cases j using Fin.cases with
      | zero => exact Real.contDiff_exp.contDiffAt.comp v0 hbd
      | succ k => exact contDiffAt_normSq_comp (hsC k)
    · cases j using Fin.cases with
      | zero => exact logPshAt_exp hbd hPb
      | succ k => exact logPshAt_normSq (hsC k)
    · have : (∑ j, u j v0) = Sv v0 := by simp [u, Sv, Fin.sum_univ_succ]
      rw [this]; exact hS0

  have hev : (fun v => ((A.ph la i (φ.symm v) + A.psD L w s ps1 η δ (φ.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun v => ((a v + ((-η) * b v + 0) + (η * Real.log (W v) + 0) + (n * Real.log (Sv v) + 0) : ℝ) : ℂ) := by
    filter_upwards [hT] with v hv
    have hx := φ.map_target hv
    have hWv : A.sqn L w (φ.symm v) = W v * Real.exp (-b v) := by
      rw [A.sqn_chart L w hD.sec_w i hx]; simp [W, b, Complex.normSq_eq_norm_sq]
    have hSv : A.sqn L s (φ.symm v) + δ = Real.exp (-b v) * Sv v := by
      rw [A.sqn_chart L s hD.sec_s i hx]
      simp only [Sv, b, Complex.normSq_eq_norm_sq, mul_add, Real.exp_add, Real.exp_log hδ]
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]; ring
    have hWp : 0 < W v := by
      have h := A.aap_sqn_pos hD (φ.symm v); rw [hWv] at h
      exact pos_of_mul_pos_left h (Real.exp_pos _).le
    have hSp : 0 < Sv v := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (s k i (φ.symm v))
      have := Real.exp_pos (b v + Real.log δ); simp only [Sv]; linarith
    unfold psD
    rw [hWv, hSv, Real.log_mul hWp.ne' (Real.exp_pos _).ne', Real.log_mul (Real.exp_pos _).ne' hSp.ne',
      Real.log_exp, A.ph_eq_sub_nsmul la L n i hx]
    simp only [a, b]; push_cast; ring
  set u4 : Fin 4 → V n → ℝ := ![a, fun v => (-η) * b v + 0,
      fun v => η * Real.log (W v) + 0, fun v => n * Real.log (Sv v) + 0]
  have hu4 : ∀ j, ContDiffAt ℝ 2 (u4 j) v0 := by
    intro j
    fin_cases j
    · exact ha
    · exact (contDiffAt_const.mul hb).add contDiffAt_const
    · exact (contDiffAt_const.mul hlW).add contDiffAt_const
    · exact (contDiffAt_const.mul hlS).add contDiffAt_const
  have hfun : (fun v => ((a v + ((-η) * b v + 0) + (η * Real.log (W v) + 0) +
      (n * Real.log (Sv v) + 0) : ℝ) : ℂ)) = fun v => ((∑ j, u4 j v : ℝ) : ℂ) := by
    funext v; simp [u4, Fin.sum_univ_four]
  have hL := hLevi i y hy ξ
  unfold leviAt at hL ⊢
  rw [leviV_congr hev, hfun, leviV_ofReal_sum hu4, Fin.sum_univ_four]
  have e1 : u4 0 = a := rfl
  have e2 : u4 1 = fun v => (-η) * b v + 0 := rfl
  have e3 : u4 2 = fun v => η * Real.log (W v) + 0 := rfl
  have e4 : u4 3 = fun v => n * Real.log (Sv v) + 0 := rfl
  rw [e1, e2, e3, e4, leviV_const_mul hb, leviV_const_mul hlW, leviV_const_mul hlS]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_nonneg hη.le hLW
  have := mul_nonneg hn0 hLS
  change η * (leviV n (fun v => ((b v : ℝ) : ℂ)) v0 ξ).re ≤ _
  change 2 * η * (leviV n (fun v => ((b v : ℝ) : ℂ)) v0 ξ).re ≤ (leviV n (fun v => ((a v : ℝ) : ℂ)) v0 ξ).re at hL
  linarith
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
