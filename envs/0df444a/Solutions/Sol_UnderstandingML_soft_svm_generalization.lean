-- Prove2me | solution 1 for UnderstandingML.soft_svm_generalization
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:20:41.001582+00:00
-- url     : https://prove2.me/submissions/10143996-897b-4994-ae8b-559c59fe40e1

import Theorems.Thm_UnderstandingML_rlm_oracle_inequality
import Definitions.Def_UnderstandingML_SVM
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

namespace SoftSVMAux

variable {d : ℕ}

/-- The hinge loss is convex in `w`. -/
theorem hinge_convexOn (z : Vec d × ℝ) : ConvexOn ℝ Set.univ (fun w ↦ hingeLoss w z) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  simp only [hingeLoss, smul_eq_mul]
  have e : 1 - z.2 * ⟪s • a + t • b, z.1⟫_ℝ =
      s * (1 - z.2 * ⟪a, z.1⟫_ℝ) + t * (1 - z.2 * ⟪b, z.1⟫_ℝ) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have : (1:ℝ) = s + t := hst.symm
    nth_rewrite 1 [this]; ring
  rw [e]
  apply max_le
  · exact add_nonneg (mul_nonneg hs (le_max_left _ _)) (mul_nonneg ht (le_max_left _ _))
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) hs)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)

/-- Lipschitz bound for the hinge loss at a point with `|y| = 1`. -/
theorem hinge_lip (z : Vec d × ℝ) (hy : z.2 = 1 ∨ z.2 = -1) (w₁ w₂ : Vec d) :
    |hingeLoss w₁ z - hingeLoss w₂ z| ≤ ‖z.1‖ * ‖w₁ - w₂‖ := by
  simp only [hingeLoss]
  have hy' : |z.2| = 1 := by rcases hy with h | h <;> rw [h] <;> simp
  calc |max 0 (1 - z.2 * ⟪w₁, z.1⟫_ℝ) - max 0 (1 - z.2 * ⟪w₂, z.1⟫_ℝ)|
      ≤ |(1 - z.2 * ⟪w₁, z.1⟫_ℝ) - (1 - z.2 * ⟪w₂, z.1⟫_ℝ)| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ = |z.2| * |⟪w₁ - w₂, z.1⟫_ℝ| := by
        rw [inner_sub_left, ← abs_mul, ← abs_neg]; ring_nf
    _ ≤ ‖z.1‖ * ‖w₁ - w₂‖ := by
        rw [hy', one_mul, mul_comm]
        exact abs_real_inner_le_norm _ _

theorem hinge_nonneg (w : Vec d) (z : Vec d × ℝ) : 0 ≤ hingeLoss w z := le_max_left _ _

/-- The hinge loss is bounded by `1 + ‖w‖ ‖x‖` when `|y| = 1`. -/
theorem hinge_le (w : Vec d) (z : Vec d × ℝ) (hy : z.2 = 1 ∨ z.2 = -1) :
    hingeLoss w z ≤ 1 + ‖w‖ * ‖z.1‖ := by
  simp only [hingeLoss]
  apply max_le (by positivity)
  have h1 : |⟪w, z.1⟫_ℝ| ≤ ‖w‖ * ‖z.1‖ := abs_real_inner_le_norm _ _
  have h2 : |z.2 * ⟪w, z.1⟫_ℝ| = |⟪w, z.1⟫_ℝ| := by
    rcases hy with h | h <;> rw [h] <;> simp
  have h3 := neg_abs_le (z.2 * ⟪w, z.1⟫_ℝ)
  linarith

theorem zeroOne_le_hinge (w : Vec d) (z : Vec d × ℝ) : zeroOneLoss w z ≤ hingeLoss w z := by
  simp only [zeroOneLoss, hingeLoss]
  split_ifs with h
  · exact le_trans (by linarith) (le_max_right _ _)
  · exact le_max_left _ _

theorem zeroOne_nonneg (w : Vec d) (z : Vec d × ℝ) : 0 ≤ zeroOneLoss w z := by
  simp only [zeroOneLoss]; split_ifs <;> norm_num

theorem hinge_continuous : Continuous (fun p : Vec d × (Vec d × ℝ) ↦ hingeLoss p.1 p.2) := by
  simp only [hingeLoss]
  fun_prop

end SoftSVMAux

open SoftSVMAux in
theorem solution {d : ℕ} (D : Measure (Vec d × ℝ)) [IsProbabilityMeasure D]
    {ρ : ℝ} (hρ : 0 < ρ) (hD : ∀ᵐ z ∂D, ‖z.1‖ ≤ ρ ∧ (z.2 = 1 ∨ z.2 = -1)) {lam : ℝ}
    (hlam : 0 < lam) (A : Learner (Vec d × ℝ) (Vec d)) (hA : IsRLMLearner hingeLoss lam A)
    (hAmeas : ∀ m, Measurable (A m)) (m : ℕ) (hm : 0 < m) (u : Vec d) :
    ∫ S, risk hingeLoss D (A m S) ∂(iidLaw D m) ≤
        risk hingeLoss D u + lam * ‖u‖ ^ 2 + 2 * ρ ^ 2 / (lam * m) ∧
    ∫ S, risk zeroOneLoss D (A m S) ∂(iidLaw D m) ≤
        risk hingeLoss D u + lam * ‖u‖ ^ 2 + 2 * ρ ^ 2 / (lam * m) := by
  classical
  set G : Set (Vec d × ℝ) := {z | ‖z.1‖ ≤ ρ ∧ (z.2 = 1 ∨ z.2 = -1)} with hGdef
  have hGmeas : MeasurableSet G := by
    have e : G = {z : Vec d × ℝ | ‖z.1‖ ≤ ρ} ∩ ({z | z.2 = 1} ∪ {z | z.2 = -1}) := by
      ext z; simp [hGdef]
    rw [e]
    exact (measurableSet_le (f := fun z : Vec d × ℝ ↦ ‖z.1‖) (g := fun _ ↦ ρ)
      (by fun_prop) measurable_const).inter
      ((measurableSet_eq_fun measurable_snd measurable_const).union
        (measurableSet_eq_fun measurable_snd measurable_const))
  set clip : Vec d × ℝ → Vec d × ℝ := G.piecewise id (fun _ ↦ ((0 : Vec d), (1 : ℝ)))
    with hclipdef
  have hclip_meas : Measurable clip := Measurable.piecewise hGmeas measurable_id measurable_const
  have hclip_mem : ∀ z, clip z ∈ G := by
    intro z
    by_cases hz : z ∈ G
    · simp only [hclipdef, Set.piecewise_eq_of_mem _ _ _ hz, id]; exact hz
    · simp only [hclipdef, Set.piecewise_eq_of_notMem _ _ _ hz]
      exact ⟨by simp [hρ.le], Or.inl rfl⟩
  have hclip_of_mem : ∀ z ∈ G, clip z = z := by
    intro z hz; simp only [hclipdef, Set.piecewise_eq_of_mem _ _ _ hz, id]
  set loss' : Vec d → Vec d × ℝ → ℝ := fun w z ↦ hingeLoss w (clip z) with hloss'
  set A' : Learner (Vec d × ℝ) (Vec d) := fun m S ↦ A m (fun i ↦ clip (S i)) with hA'def
  -- hypotheses of the oracle inequality for the clipped problem
  have hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss' w z) := fun z ↦ hinge_convexOn _
  have hlip : IsLipschitzLoss ρ loss' := by
    intro z w₁ w₂
    have hm := hclip_mem z
    calc |loss' w₁ z - loss' w₂ z| ≤ ‖(clip z).1‖ * ‖w₁ - w₂‖ := hinge_lip _ hm.2 _ _
      _ ≤ ρ * ‖w₁ - w₂‖ := mul_le_mul_of_nonneg_right hm.1 (norm_nonneg _)
  have hA' : IsRLMLearner loss' lam A' := fun m S w' ↦ hA m (fun i ↦ clip (S i)) w'
  have hmeas : Measurable (Function.uncurry loss') := by
    have : Function.uncurry loss' =
        (fun p : Vec d × (Vec d × ℝ) ↦ hingeLoss p.1 p.2) ∘ (fun p ↦ (p.1, clip p.2)) := rfl
    rw [this]
    exact hinge_continuous.measurable.comp (measurable_fst.prodMk (hclip_meas.comp measurable_snd))
  have hnonneg : ∀ w z, 0 ≤ loss' w z := fun w z ↦ hinge_nonneg _ _
  have hC : ∀ z, loss' 0 z ≤ 1 := fun z ↦ by simp [hloss', hingeLoss]
  have hAmeas' : ∀ m, Measurable (A' m) := fun m ↦
    (hAmeas m).comp (measurable_pi_lambda _ fun i ↦ hclip_meas.comp (measurable_pi_apply i))
  have key := rlm_oracle_inequality loss' hconv hlip hlam A' hA' hmeas hnonneg hC hAmeas' D m hm u
  -- the clipped risk agrees with the hinge risk
  have hrisk : ∀ w, risk loss' D w = risk hingeLoss D w := by
    intro w
    apply integral_congr_ae
    filter_upwards [hD] with z hz
    simp only [hloss', hclip_of_mem z hz]
  -- almost every sample lies in `G`
  have hSG : ∀ᵐ S ∂(iidLaw D m), ∀ i, S i ∈ G := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin m ↦ D) i).quasiMeasurePreserving.ae hD
  have hAA' : ∀ᵐ S ∂(iidLaw D m), A' m S = A m S := by
    filter_upwards [hSG] with S hS
    simp only [hA'def]
    congr 1
    funext i
    exact hclip_of_mem _ (hS i)
  have hint_eq : ∫ S, risk hingeLoss D (A m S) ∂(iidLaw D m) =
      ∫ S, risk loss' D (A' m S) ∂(iidLaw D m) := by
    apply integral_congr_ae
    filter_upwards [hAA'] with S hS
    rw [hS, hrisk]
  have part1 : ∫ S, risk hingeLoss D (A m S) ∂(iidLaw D m) ≤
      risk hingeLoss D u + lam * ‖u‖ ^ 2 + 2 * ρ ^ 2 / (lam * m) := by
    rw [hint_eq, ← hrisk u]; exact key
  refine ⟨part1, le_trans ?_ part1⟩
  -- the 0-1 part
  have hprob : IsProbabilityMeasure (iidLaw D m) := by
    unfold iidLaw; infer_instance
  -- norm bound on the learner's output
  have hnormA : ∀ S, ‖A' m S‖ ≤ 1 + 1 / lam := by
    intro S
    have h0 := hA' m S 0
    simp only [rlmObjective, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero] at h0
    have hemp0 : empRisk loss' S 0 = 1 := by
      simp only [empRisk, hloss', hingeLoss, inner_zero_left, mul_zero, sub_zero,
        max_eq_right zero_le_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      field_simp
    have hempA : 0 ≤ empRisk loss' S (A' m S) := by
      unfold empRisk
      exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hnonneg _ _) (Nat.cast_nonneg _)
    rw [hemp0] at h0
    have hsq : lam * ‖A' m S‖ ^ 2 ≤ 1 := by linarith
    have hn := norm_nonneg (A' m S)
    rcases le_or_gt ‖A' m S‖ 1 with h1 | h1
    · have : 0 ≤ 1 / lam := by positivity
      linarith
    · have : ‖A' m S‖ ≤ ‖A' m S‖ ^ 2 := by nlinarith
      have : ‖A' m S‖ ^ 2 ≤ 1 / lam := by rw [le_div_iff₀ hlam]; linarith
      linarith
  have hriskbound : ∀ w, ‖risk loss' D w‖ ≤ 1 + ‖w‖ * ρ := by
    intro w
    have := norm_integral_le_of_norm_le_const (μ := D) (f := fun z ↦ loss' w z)
      (C := 1 + ‖w‖ * ρ) (Filter.Eventually.of_forall fun z ↦ by
        have hm := hclip_mem z
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _ _)]
        calc loss' w z ≤ 1 + ‖w‖ * ‖(clip z).1‖ := hinge_le _ _ hm.2
          _ ≤ 1 + ‖w‖ * ρ := by gcongr; exact hm.1)
    simpa [risk] using this
  have hsm : StronglyMeasurable (fun w ↦ risk loss' D w) := by
    have : StronglyMeasurable (Function.uncurry loss') := hmeas.stronglyMeasurable
    exact this.integral_prod_right'
  have hint' : Integrable (fun S ↦ risk loss' D (A' m S)) (iidLaw D m) := by
    refine Integrable.of_bound (hsm.comp_measurable (hAmeas' m)).aestronglyMeasurable
      (1 + (1 + 1 / lam) * ρ) (Filter.Eventually.of_forall fun S ↦ ?_)
    calc ‖risk loss' D (A' m S)‖ ≤ 1 + ‖A' m S‖ * ρ := hriskbound _
      _ ≤ 1 + (1 + 1 / lam) * ρ := by gcongr; exact hnormA S
  have hint : Integrable (fun S ↦ risk hingeLoss D (A m S)) (iidLaw D m) := by
    refine hint'.congr ?_
    filter_upwards [hAA'] with S hS
    rw [hS, hrisk]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun S ↦ integral_nonneg fun z ↦ zeroOne_nonneg _ _
  · exact hint
  · refine Filter.Eventually.of_forall fun S ↦ ?_
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun z ↦ zeroOne_nonneg _ _
    · refine Integrable.of_bound
        (hinge_continuous.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
        (1 + ‖A m S‖ * ρ) ?_
      filter_upwards [hD] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hinge_nonneg _ _)]
      calc hingeLoss (A m S) z ≤ 1 + ‖A m S‖ * ‖z.1‖ := hinge_le _ _ hz.2
        _ ≤ 1 + ‖A m S‖ * ρ := by gcongr; exact hz.1
    · exact Filter.Eventually.of_forall fun z ↦ zeroOne_le_hinge _ _
