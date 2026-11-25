-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_proof_36490bd2ce50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:22.512584+00:00
-- url     : https://prove2.me/submissions/42065b39-a0d4-4486-b54e-4a56b5039cf2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_analyticAt_of_isSheetAt_53bfd87cf7f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_maDens_cons_eq_zero_7292b531e842
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_abs_sheetSum_sub_le_cf344494087b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_integrable_chartDens_a8487f280a6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_integrable_ball_2bd9babf2f75
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_term_bound_3573df0163f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_final_bound_c07343cad33a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffGradient_proof_81aaa98bdfc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartAbsDens_nonneg_5c6d71b76cc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_vecCons_comp_613af14c7f72


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open CutOffBoundaryBound
namespace GroundTheory.Heights₂.Heights
namespace CutOffBoundaryBound
theorem _root_.solution (hM : ChartMassCompact.Statement) (hL : MaDensLeibniz.Statement)
    (hN : EnergyDensNonneg.Statement) (hS : GradDensSheetBound.Statement) :
    CutOffBoundaryBound.Statement := by
  intro n d J A F G φ hJ hdim hA hF hG hφ hc
  obtain ⟨UF, hUFo, hZF, hFs⟩ := hF
  obtain ⟨UG, hUGo, hZG, hGs⟩ := hG
  choose Uφ hUφo hZφ hφs using hφ
  have hUo : IsOpen (UF ∩ UG ∩ ⋂ i, Uφ i) := (hUFo.inter hUGo).inter (isOpen_iInter_of_finite hUφo)
  set U := UF ∩ UG ∩ ⋂ i, Uφ i with hUdef
  have hZU : zeroSet J ⊆ U := Set.subset_inter (Set.subset_inter hZF hZG) (Set.subset_iInter hZφ)
  have hFU : ContDiffOn ℝ ∞ F U := hFs.mono fun x hx => hx.1.1
  have hGU : ContDiffOn ℝ ∞ G U := hGs.mono fun x hx => hx.1.2
  have hφU : ∀ i, ContDiffOn ℝ ∞ (φ i) U := fun i => (hφs i).mono fun x hx => Set.mem_iInter.1 hx.2 i
  have hFc : ContinuousOn F (zeroSet J) := hFU.continuousOn.mono hZU
  have hGc : ContinuousOn G (zeroSet J) := hGU.continuousOn.mono hZU
  have hle2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hZc := SheetSumMeasurable.isClosed_zeroSet J

  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  have hK : IsCompact (zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R) :=
    (isCompact_closedBall 0 R).inter_left hZc
  obtain ⟨C₁, hC₁0, hC₁⟩ := hS n d φ U _ hUo hK (fun x hx => hZU hx.1)
    (fun i => (hφU i).of_le hle2)
  obtain ⟨M₀, hM₀⟩ := (hc.isCompact.inter_left hZc).exists_bound_of_continuousOn
    (f := fun x => G x * F x) ((hGc.mul hFc).mono Set.inter_subset_left)
  have hMb : ∀ x ∈ zeroSet J, |G x * F x| ≤ max M₀ 0 := by
    intro x hx
    by_cases hxF : x ∈ tsupport F
    · exact (by simpa [Real.norm_eq_abs] using hM₀ x ⟨hx, hxF⟩ : |G x * F x| ≤ M₀).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hxF, mul_zero, abs_zero]
      exact le_max_right _ _

  have hcons : ∀ (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ), SmoothNear (zeroSet J) f →
      (∀ i, SmoothNear (zeroSet J) (ψ i)) → ∀ i, SmoothNear (zeroSet J) (vecCons f ψ i) := by
    intro f ψ hf hψ i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hψ i
  have hω : ∀ i : Fin d, SmoothNear (zeroSet J) ((fun _ => euclPot) i : (Fin n → ℂ) → ℝ) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
  have hφn : ∀ i, SmoothNear (zeroSet J) (φ i) := fun i => ⟨U, hUo, hZU, hφU i⟩
  have hFn : SmoothNear (zeroSet J) F := ⟨U, hUo, hZU, hFU⟩
  have hF2n : SmoothNear (zeroSet J) (fun x => F x ^ 2 / 2) := ⟨U, hUo, hZU, (hFU.pow 2).div_const 2⟩
  have hF2c : HasCompactSupport (fun x => F x ^ 2 / 2) := hc.mono fun x hx h0 => hx (by simp [h0])
  have hf₁ := integrable_chartDens hM hJ hdim hA (f := fun x => G x ^ 2) (hGc.pow 2) (hcons _ _ hF2n hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hF2c⟩)
  have hf₂ := integrable_chartDens hM hJ hdim hA (f := fun x => G x ^ 2 * F x) ((hGc.pow 2).mul hFc) (hcons _ _ hFn hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hc⟩)
  set Φ := ∫ y, (chartDens J A (fun x => G x ^ 2) (vecCons (fun x => F x ^ 2 / 2) fun _ => euclPot) y -
    chartDens J A (fun x => G x ^ 2 * F x) (vecCons F fun _ => euclPot) y) with hΦ
  refine ⟨R, max (max M₀ 0) (2 * C₁ * √(max Φ 1)), fun χ hχ => ?_⟩
  have hχc : Continuous χ := hχ.continuous
  have hχn : SmoothNear (zeroSet J) χ := smoothNear_of_contDiff hχ
  have hχFn : SmoothNear (zeroSet J) (fun x => χ x * F x) := ⟨U, hUo, hZU, hχ.contDiffOn.mul hFU⟩
  have hχ2n : SmoothNear (zeroSet J) (fun x => χ x ^ 2 / 2) := smoothNear_of_contDiff ((hχ.pow 2).div_const 2)
  have hD₁ := integrable_chartDens hM hJ hdim hA hGc (hcons _ _ hχFn hφn)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact (hc.mul_left : HasCompactSupport (χ * F))⟩)
  have hD₂ := integrable_chartDens hM hJ hdim hA (f := fun x => χ x * G x) (hχc.continuousOn.mul hGc) (hcons _ _ hFn hφn)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hc⟩)
  have ha := (integrable_ball hM hJ hdim hA R (w := fun _ => (1 : ℝ)) continuous_const (hcons _ _ hχn hφn)).1
  have he₁ := (integrable_ball hM hJ hdim hA R (w := fun _ => (1 : ℝ)) continuous_const (hcons _ _ hχ2n hω)).2
  have he₂ := (integrable_ball hM hJ hdim hA R hχc (hcons _ _ hχn hω)).2

  have key : ∀ t > 0, ∀ y, |chartDens J A G (vecCons (fun x => χ x * F x) φ) y -
      chartDens J A (fun x => χ x * G x) (vecCons F φ) y| ≤
      max M₀ 0 * chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1) (vecCons χ φ) y +
      C₁ * t * (chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
          (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) y -
        chartDens J A ((Metric.closedBall 0 R).indicator χ) (vecCons χ fun _ => euclPot) y) +
      C₁ / t * (chartDens J A (fun x => G x ^ 2) (vecCons (fun x => F x ^ 2 / 2) fun _ => euclPot) y -
        chartDens J A (fun x => G x ^ 2 * F x) (vecCons F fun _ => euclPot) y) := by
    intro t ht y
    have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
    unfold chartDens chartAbsDens
    refine abs_sheetSum_sub_le hfin _ _ _ _ _ _ _ _ _ _ fun x hx s hs => ?_
    obtain ⟨hxZ, hAx⟩ := hx
    have hsx : s y = x := by
      obtain ⟨_, _, _, _, h, -⟩ := hs
      rw [← hAx]
      exact h
    have han : AnalyticAt ℂ s y := by
      rw [← hAx]
      exact analyticAt_of_isSheetAt hs
    have hsc : ContDiffAt ℝ 2 s y := han.restrictScalars.contDiffAt
    have hxU : s y ∈ U := hsx ▸ hZU hxZ
    have c2 : ∀ g : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ g U → ContDiffAt ℝ 2 (g ∘ s) y := fun g hg =>
      ((hg.contDiffAt (hUo.mem_nhds hxU)).of_le hle2).comp y hsc
    have hχs := c2 χ hχ.contDiffOn
    have hFs' := c2 F hFU
    simp only [vecCons_comp]
    have e₂ : maDens (Fin.cons ((fun x => χ x ^ 2 / 2) ∘ s) fun _ => euclPot ∘ s) y =
        (χ ∘ s) y * maDens (Fin.cons (χ ∘ s) fun _ => euclPot ∘ s) y +
          gradDens (fun _ => euclPot ∘ s) (χ ∘ s) (χ ∘ s) y :=
      (hL d (fun _ => euclPot ∘ s) (χ ∘ s) (χ ∘ s) y hχs hχs).2
    have e₃ : maDens (Fin.cons ((fun x => F x ^ 2 / 2) ∘ s) fun _ => euclPot ∘ s) y =
        (F ∘ s) y * maDens (Fin.cons (F ∘ s) fun _ => euclPot ∘ s) y +
          gradDens (fun _ => euclPot ∘ s) (F ∘ s) (F ∘ s) y :=
      (hL d (fun _ => euclPot ∘ s) (F ∘ s) (F ∘ s) y hFs' hFs').2
    rw [e₂, e₃]
    simp only [Function.comp_apply, hsx]
    have hEχ := hN n d s y (χ ∘ s) han
    have hEF := hN n d s y (F ∘ s) han
    have hQ : ∀ m E : ℝ, (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x * (χ x * m + E) -
        (Metric.closedBall (0 : Fin n → ℂ) R).indicator χ x * m =
          (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x * E := by
      intro m E
      by_cases hB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
      · rw [Set.indicator_of_mem hB, Set.indicator_of_mem hB]
        ring
      · rw [Set.indicator_of_notMem hB, Set.indicator_of_notMem hB]
        ring
    rw [hQ, show ∀ m E : ℝ, G x ^ 2 * (F x * m + E) - G x ^ 2 * F x * m = G x ^ 2 * E from
      fun m E => by ring]
    by_cases hxF : x ∈ tsupport F
    · have hxB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := hR hxF
      have hKs : s y ∈ zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R := hsx ▸ ⟨hxZ, hxB⟩
      have e₁ : maDens (Fin.cons ((fun x => χ x * F x) ∘ s) fun i => φ i ∘ s) y =
          (χ ∘ s) y * maDens (Fin.cons (F ∘ s) fun i => φ i ∘ s) y +
            (F ∘ s) y * maDens (Fin.cons (χ ∘ s) fun i => φ i ∘ s) y +
              gradDens (fun i => φ i ∘ s) (χ ∘ s) (F ∘ s) y + gradDens (fun i => φ i ∘ s) (F ∘ s) (χ ∘ s) y :=
        (hL d (fun i => φ i ∘ s) (χ ∘ s) (F ∘ s) y hχs hFs').1
      rw [e₁]
      simp only [Function.comp_apply, hsx]
      rw [Set.indicator_of_mem hxB]
      exact term_bound ht hC₁0 (hMb x hxZ) hEχ hEF (hC₁ s y _ _ han hKs) (hC₁ s y _ _ han hKs)
    · have hev : ∀ᶠ z in 𝓝 y, s z ∉ tsupport F :=
        han.continuousAt.preimage_mem_nhds ((isClosed_tsupport F).isOpen_compl.mem_nhds (hsx ▸ hxF))
      have hF0 : (F ∘ s) =ᶠ[𝓝 y] fun _ => 0 :=
        hev.mono fun z hz => image_eq_zero_of_notMem_tsupport (f := F) hz
      have hχF0 : ((fun x => χ x * F x) ∘ s) =ᶠ[𝓝 y] fun _ => 0 :=
        hev.mono fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
      rw [maDens_cons_eq_zero _ _ y hχF0, maDens_cons_eq_zero _ _ y hF0, mul_zero, mul_zero, sub_zero,
        abs_zero]
      have hi : 0 ≤ (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      exact add_nonneg (add_nonneg (mul_nonneg (le_max_right _ _) (abs_nonneg _))
        (mul_nonneg (mul_nonneg hC₁0 ht.le) (mul_nonneg hi hEχ)))
        (mul_nonneg (div_nonneg hC₁0 ht.le) (mul_nonneg (sq_nonneg _) hEF))

  refine final_bound hC₁0 (integral_nonneg fun y => chartAbsDens_nonneg J A _ _ y)
    fun t ht => ?_
  set D₁ := chartDens J A G (vecCons (fun x => χ x * F x) φ) with hD₁def
  set D₂ := chartDens J A (fun x => χ x * G x) (vecCons F φ) with hD₂def
  set a := chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1) (vecCons χ φ) with hadef
  set e₁ := chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
    (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) with he₁def
  set e₂ := chartDens J A ((Metric.closedBall 0 R).indicator χ) (vecCons χ fun _ => euclPot) with he₂def
  set f₁ := chartDens J A (fun x => G x ^ 2) (vecCons (fun x => F x ^ 2 / 2) fun _ => euclPot) with hf₁def
  set f₂ := chartDens J A (fun x => G x ^ 2 * F x) (vecCons F fun _ => euclPot) with hf₂def
  have h1 : chartInt J A G (vecCons (fun x => χ x * F x) φ) -
      chartInt J A (fun x => χ x * G x) (vecCons F φ) = ∫ y, (D₁ y - D₂ y) := (integral_sub hD₁ hD₂).symm
  have h2 : energyInt J A (Metric.closedBall 0 R) χ = ∫ y, (e₁ y - e₂ y) := (integral_sub he₁ he₂).symm
  have h3 : ∫ y, (max M₀ 0 * a y + C₁ * t * (e₁ y - e₂ y) + C₁ / t * (f₁ y - f₂ y)) =
      max M₀ 0 * (∫ y, a y) + C₁ * t * (∫ y, (e₁ y - e₂ y)) + C₁ / t * Φ := by
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
    all_goals first
      | exact ha.const_mul _
      | exact (he₁.sub he₂).const_mul _
      | exact (hf₁.sub hf₂).const_mul _
      | exact (ha.const_mul _).add ((he₁.sub he₂).const_mul _)
  rw [h1, h2, ← h3]
  refine le_trans ?_ (integral_mono (hD₁.sub hD₂).abs (((ha.const_mul _).add ((he₁.sub he₂).const_mul _)).add
    ((hf₁.sub hf₂).const_mul _)) fun y => key t ht y)
  exact (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm fun y => D₁ y - D₂ y :
    |∫ y, (D₁ y - D₂ y)| ≤ ∫ y, |D₁ y - D₂ y|)
end CutOffBoundaryBound
end GroundTheory.Heights₂.Heights
