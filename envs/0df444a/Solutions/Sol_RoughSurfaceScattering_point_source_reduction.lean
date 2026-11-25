-- Prove2me | solution 1 for RoughSurfaceScattering.point_source_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T06:40:58.320855+00:00
-- url     : https://prove2.me/submissions/3ba0e9fa-8c05-4114-9f44-348419b895f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_tsp_stability_h1
import Theorems.Thm_RoughSurfaceScattering_phi_tsp_lower
import Theorems.Thm_RoughSurfaceScattering_point_source_data_bound

open MeasureTheory
open RoughSurfaceScattering

lemma abs_coord_le_norm (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

lemma normal_norm (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < arcDen f s := Real.sqrt_pos.mpr (by positivity)
  have hpt : ‖pt (deriv f s) (-1)‖ = arcDen f s := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [pt, arcDen]
    ring_nf
  rw [normal, norm_smul, hpt, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- Mirror of `cone_below_interface`: points in a cone around `-n` lie above `Γ`. -/
lemma cone_above_interface (f : ℝ → ℝ) (s0 : ℝ) (hf : DifferentiableAt ℝ f s0) :
    ∃ r > (0 : ℝ), ∀ v : R2, v ≠ 0 → ‖v‖ < r →
      ‖v‖ ≤ -(2 * @inner ℝ R2 _ v (normal f s0)) → gpt f s0 + v ∈ Dplus f := by
  set d := deriv f s0 with hd
  set a := arcDen f s0 with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hlo := hf.hasDerivAt.isLittleO
  have hev := hlo.def (c := a / 4) (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, fun v hv0 hvr hcone => ?_⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hinner : @inner ℝ R2 _ v (normal f s0) = a⁻¹ * (d * v 0 - v 1) := by
    simp [normal, pt, ← ha, ← hd, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_right]
    ring_nf
    try simp
  rw [hinner] at hcone
  have hkey : a * ‖v‖ ≤ 2 * (v 1 - d * v 0) := by
    have := mul_le_mul_of_nonneg_left hcone hapos.le
    calc a * ‖v‖ ≤ a * -(2 * (a⁻¹ * (d * v 0 - v 1))) := this
      _ = 2 * (v 1 - d * v 0) := by field_simp; ring
  have h0 := abs_coord_le_norm v 0
  have hdist : dist (s0 + v 0) s0 < r := by
    rw [Real.dist_eq, add_sub_cancel_left]; linarith
  have htay := hball hdist
  simp only [add_sub_cancel_left, Real.norm_eq_abs, smul_eq_mul] at htay
  have hup : f (s0 + v 0) ≤ f s0 + v 0 * d + a / 4 * |v 0| := by
    have := (abs_le.mp htay).2
    linarith
  show f ((gpt f s0 + v) 0) < (gpt f s0 + v) 1
  simp only [gpt, pt, PiLp.add_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have : a / 4 * |v 0| ≤ a / 4 * ‖v‖ := mul_le_mul_of_nonneg_left h0 (by positivity)
  nlinarith

lemma supNormGam_nonneg {E : Type*} [NormedAddCommGroup E] (φ : ℝ → E) :
    0 ≤ supNormGam φ := Real.iSup_nonneg fun _ => norm_nonneg _

lemma holderNorm0_nonneg {E : Type*} [NormedAddCommGroup E] (f : ℝ → ℝ) (α : ℝ) (φ : ℝ → E) :
    0 ≤ holderNorm0 f α φ :=
  add_nonneg (supNormGam_nonneg φ) (Real.iSup_nonneg fun _ => by positivity)

lemma holderNorm1_nonneg (f : ℝ → ℝ) (α : ℝ) (φ : ℝ → ℂ) : 0 ≤ holderNorm1 f α φ :=
  add_nonneg (supNormGam_nonneg φ) (holderNorm0_nonneg f α _)

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∀ χ : R2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
          (∀ x ∈ Metric.ball (gpt f s0) 1, χ x = 1) →
        ∀ u W : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).1
            (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).2
            (u j).1 (u j).2) →
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (fun s => ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) *
              Phi kp (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0))
            (fun _ => 0) (W j).1 (W j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => (u j).2 x - ((μ⁻¹ : ℝ) : ℂ) *
              Phi km x (gpt f s0 - (δ / (j : ℝ)) • normal f s0) - (W j).2 x) ≤
              ENNReal.ofReal C := by
  obtain ⟨r, hr, hcone⟩ := cone_above_interface f s0 (hf.1 s0)
  obtain ⟨δ3, hδ3, hdata⟩ := point_source_data_bound f hf lam hlam0 hlam1 hf2 kp km μ hpar s0
  refine ⟨min r δ3, lt_min hr hδ3,
    fun δ hδ hδ0 D0 hD0 hball hsub χ hχ1 hχ2 hχ3 u W hu hW => ?_⟩
  have hδr : δ < r := lt_of_lt_of_le hδ0 (min_le_left _ _)
  obtain ⟨C3, hC3⟩ := hdata δ hδ (lt_of_lt_of_le hδ0 (min_le_right _ _)) χ hχ1 hχ2 hχ3
    (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨C1, hC1⟩ := tsp_stability_h1 f hf kp km μ hpar (1 / 2) (by norm_num) (by norm_num)
    D0 hD0.1 hD0.2.2.1 hsub
  have hn1 := normal_norm f s0
  have hn0 : normal f s0 ≠ 0 := fun h => by rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  refine ⟨max C1 0 * max C3 0, fun j hj => ?_⟩
  set xj := gpt f s0 - (δ / (j : ℝ)) • normal f s0 with hxjdef
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht : 0 < δ / (j : ℝ) := by positivity
  have hxj : xj ∈ Dplus f := by
    have hnv : ‖-((δ / (j : ℝ)) • normal f s0)‖ = δ / j := by
      rw [norm_neg, norm_smul, hn1, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    have := hcone (-((δ / (j : ℝ)) • normal f s0))
      (by rw [neg_ne_zero]; exact smul_ne_zero ht.ne' hn0)
      (by rw [hnv]; linarith [div_le_self hδ.le hj'])
      (by
        rw [hnv, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq, hn1]
        simp only [one_pow, mul_one, RCLike.conj_to_real]
        linarith)
    rwa [← sub_eq_add_neg] at this
  have hV := phi_tsp_lower f hf kp km μ hpar xj hxj ((μ⁻¹ : ℝ) : ℂ)
  obtain ⟨hd1, hd2, hdn⟩ := hC3 j hj
  have h := hC1 _ _ _ _ _ _ _ _ _ _ _ _ (hu j hj) (hW j hj) hV hd1 hd2
  have heq : (fun x => (u j).2 x - (W j).2 x - ((μ⁻¹ : ℝ) : ℂ) * Phi km x xj) =
      fun x => (u j).2 x - ((μ⁻¹ : ℝ) : ℂ) * Phi km x xj - (W j).2 x := by
    funext x; ring
  rw [heq] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hX0 : 0 ≤ holderNorm1 f (1 / 2) (fun s =>
          (incData f (pointSource kp xj)).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) * Phi kp (gpt f s) xj -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) xj)) +
        holderNorm0 f (1 / 2) (fun s =>
          (incData f (pointSource kp xj)).2 s - 0 -
          -((μ : ℂ) * (((μ⁻¹ : ℝ) : ℂ) * fderiv ℝ
            (fun x => Phi km x xj) (gpt f s) (normal f s)))) :=
    add_nonneg (holderNorm1_nonneg _ _ _) (holderNorm0_nonneg _ _ _)
  calc C1 * _ ≤ max C1 0 * _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    _ ≤ max C1 0 * max C3 0 :=
        mul_le_mul_of_nonneg_left (hdn.trans (le_max_left _ _)) (le_max_right _ _)
