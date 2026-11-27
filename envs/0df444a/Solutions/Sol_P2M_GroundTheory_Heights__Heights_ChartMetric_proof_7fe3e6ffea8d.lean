-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMetric_proof_7fe3e6ffea8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:29.147137+00:00
-- url     : https://prove2.me/submissions/2612a77c-7e87-453c-a24a-a50cd75c31f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_contDiff_evalCone_7f1d32aee91e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_scale_b69d59385d69
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_pos_aa6df2a90236
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_den_scale_816ca627b582
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_scale_alg_9e8d282e6431
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_vectorL2Norm_conj_a383f706a1f4


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
open MvPolynomial
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric
namespace GroundTheory.Heights₂.Heights.ChartMetric
theorem _root_.solution (hDen : ChartDenominatorAlt.Statement) (hPts : ConePoints.Statement) (hCross : ChartCrossRatio.Statement) :
    ChartMetric.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG
  have hDen' := hDen ι n P D d g hg r G δ hG
  have hold : ContDiff ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ (D.basePart₂ w : Cone n ℂ)) :=
    contDiff_pi.2 fun k ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) (some k)).contDiff
  have hmaps : Set.MapsTo (fun w : Cone D.extSizes ℂ ↦ (D.basePart₂ w : Cone n ℂ))
      {w | BlockNonzero w} {z | BlockNonzero z} := fun w hw k ↦ hw (some k)
  refine ⟨⟨HermLine.mk (n := D.extSizes) AddBlockData.newDeg (D.plusMetric N d g G δ) ?pos ?smul ?smooth, rfl, fun w _ ↦ rfl, ?conj⟩, ?pts⟩
  case pos =>
    intro w hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    unfold AddBlockData.plusMetric
    exact mul_pos (mul_pos (N.metric_pos _ hz) (vectorL2Norm_pos (hw none)))
      (Real.sqrt_pos.mpr (div_pos (chartSum_pos hz d) (hDen'.1 _ hz)))
  case smul =>
    intro t w ht hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    have ht' : ∀ k, t (some k) ≠ 0 := fun k ↦ ht (some k)
    have hpos : ∀ k, 0 < ‖t (some k)‖ := fun k ↦ norm_pos_iff.mpr (ht' k)
    have hdeg : ∏ o, ‖t o‖ ^ AddBlockData.newDeg o = ‖t none‖ := by
      rw [Fintype.prod_option]
      simp [AddBlockData.newDeg]
    have hm := N.metric_smul (fun k ↦ t (some k)) (D.basePart₂ w) ht' hz
    have hs := chartSum_scale (fun k ↦ t (some k)) (D.basePart₂ w) d
    have hd := den_scale D hg hG (fun k ↦ t (some k)) ht' (D.basePart₂ w)
    beta_reduce at hm hs hd
    have hC : ∏ k, ‖t (some k)‖ ^ (2 * ((d k : ℤ) + D.deg k)) =
        (∏ k, ‖t (some k)‖ ^ (2 * (d k : ℤ))) * (∏ k, ‖t (some k)‖ ^ D.deg k) ^ 2 := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hpos k).ne']
      congr 1
      push_cast
      ring
    show D.plusMetric N d g G δ (fun o i ↦ t o * w o i) =
      (∏ o, ‖t o‖ ^ AddBlockData.newDeg o) * D.plusMetric N d g G δ w
    have eold : D.basePart₂ (fun o i ↦ t o * w o i) = fun k i ↦ t (some k) * D.basePart₂ w k i := rfl
    have enew : D.newPart (fun o i ↦ t o * w o i) = fun i ↦ t none * D.newPart w i := rfl
    unfold AddBlockData.plusMetric
    rw [eold, enew, hdeg, hm, vectorL2Norm_const_mul, hs, hd, hC, hN]
    exact scale_alg _ _ _ _ _ _ _ (Finset.prod_pos fun k _ ↦ zpow_pos (hpos k) _)
      (Finset.prod_pos fun k _ ↦ zpow_pos (hpos k) _) (hDen'.1 _ hz)
  case smooth =>
    have h1 : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ N.metric (D.basePart₂ w)) {w | BlockNonzero w} :=
      N.metric_smooth.comp hold.contDiffOn hmaps
    have h2 : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ l2Norm (D.newPart w)) {w | BlockNonzero w} :=
      contDiffOn_l2Norm_block (n := D.extSizes) none
    have hS : ContDiff ℝ ∞ (fun w : Cone D.extSizes ℂ ↦
        ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2) :=
      ContDiff.sum fun c _ ↦ (contDiff_norm_sq ℝ).comp ((contDiff_evalCone _).comp hold)
    have hDn : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ D.den d g G δ (D.basePart₂ w)) {w | BlockNonzero w} :=
      hDen'.2.comp hold.contDiffOn hmaps
    have h3 := (hS.contDiffOn.div hDn fun w hw ↦ (hDen'.1 _ (hmaps hw)).ne').sqrt fun w hw ↦
      (div_pos (chartSum_pos (hmaps hw) d) (hDen'.1 _ (hmaps hw))).ne'
    exact (h1.mul h2).mul h3
  case conj =>
    intro hNc w hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    have hN' : N.metric (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) = N.metric (D.basePart₂ w) := hNc _ hz
    have hev : ∀ f : MvPolynomial (Coord n) ℤ, evalCone (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) f =
        starRingEnd ℂ (evalCone (D.basePart₂ w) f) :=
      fun f ↦ evalCone_map (starRingEnd ℂ) (D.basePart₂ w) f
    have hS : ∑ c : (k : ι) → Fin (n k + 1),
        ‖evalCone (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) (chartMonomial c d)‖ ^ 2 =
        ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2 := by
      simp only [hev, Complex.norm_conj]
    have hD : D.den d g G δ (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) = D.den d g G δ (D.basePart₂ w) := by
      unfold AddBlockData.den
      simp only [hev, Complex.norm_conj, vectorL2Norm_conj]
    have eold : D.basePart₂ (fun o i ↦ starRingEnd ℂ (w o i)) = fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i) := rfl
    have enew : D.newPart (fun o i ↦ starRingEnd ℂ (w o i)) = fun i ↦ starRingEnd ℂ (D.newPart w i) := rfl
    show D.plusMetric N d g G δ (fun o i ↦ starRingEnd ℂ (w o i)) = D.plusMetric N d g G δ w
    unfold AddBlockData.plusMetric
    rw [eold, enew, vectorL2Norm_conj, hN', hS, hD]
  case pts =>
    intro w hw c la hm hz'
    obtain ⟨hzP, -⟩ := (hPts ι n P D d g hg).2 w hw
    have hG0 : ∀ i, evalCone (D.basePart₂ w) (G i) = 0 := fun i ↦
      hzP.2 _ (by rw [← hG.span_eq]; exact Ideal.subset_span ⟨i, rfl⟩)
    have hcr : ∀ c' j, evalCone (D.basePart₂ w) (chartMonomial c' d) * evalCone (D.basePart₂ w) (g c j) =
        evalCone (D.basePart₂ w) (chartMonomial c d) * evalCone (D.basePart₂ w) (g c' j) := by
      intro c' j
      have h := hzP.2 _ (hCross ι n P D d g hg c c' j)
      unfold evalCone at h ⊢
      rw [eval₂_sub, eval₂_mul, eval₂_mul, sub_eq_zero] at h
      exact h
    have hla : ∀ c' j, D.newPart w j * evalCone (D.basePart₂ w) (chartMonomial c' d) =
        la * evalCone (D.basePart₂ w) (g c' j) := by
      intro c' j
      rw [hz' j, div_mul_eq_mul_div, div_eq_iff hm, mul_assoc, mul_comm (evalCone _ (g c j)), hcr c' j]
      ring
    have hl2 : l2Norm (D.newPart w) ^ 2 = ∑ j, ‖D.newPart w j‖ ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    have hden : D.den d g G δ (D.basePart₂ w) = ∑ c', ∑ j, ‖evalCone (D.basePart₂ w) (g c' j)‖ ^ 2 := by
      simp [AddBlockData.den, hG0]
    have key : l2Norm (D.newPart w) ^ 2 * ∑ c', ‖evalCone (D.basePart₂ w) (chartMonomial c' d)‖ ^ 2 =
        ‖la‖ ^ 2 * D.den d g G δ (D.basePart₂ w) := by
      rw [hl2, hden, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ ↦ ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have e := congrArg (fun x : ℂ ↦ ‖x‖ ^ 2) (hla c' j)
      simp only [norm_mul, mul_pow] at e
      exact e
    have hDpos : 0 < D.den d g G δ (D.basePart₂ w) := hDen'.1 _ hzP.1
    have hL : 0 ≤ l2Norm (D.newPart w) := Real.sqrt_nonneg _
    have e : l2Norm (D.newPart w) *
        Real.sqrt ((∑ c', ‖evalCone (D.basePart₂ w) (chartMonomial c' d)‖ ^ 2) / D.den d g G δ (D.basePart₂ w)) =
        ‖la‖ := by
      rw [← Real.sqrt_sq hL, ← Real.sqrt_mul (sq_nonneg _), ← mul_div_assoc, key, mul_div_assoc,
        div_self hDpos.ne', mul_one, Real.sqrt_sq (norm_nonneg _)]
    unfold AddBlockData.plusMetric
    rw [mul_assoc, e, mul_comm]
end GroundTheory.Heights₂.Heights.ChartMetric
