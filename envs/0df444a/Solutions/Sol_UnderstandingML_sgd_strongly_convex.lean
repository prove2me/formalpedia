-- Prove2me | solution 1 for UnderstandingML.sgd_strongly_convex
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:42:53.680988+00:00
-- url     : https://prove2.me/submissions/8ccdd7a2-7986-4bc9-9281-502f70761171

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

/-- The expected direction of an oracle with bounded second moment has norm at most `1 + ρ²`. -/
lemma norm_integral_le_of_moment {d : ℕ} {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] (g : Vec d → Z → Vec d) (hg : Measurable (Function.uncurry g))
    {ρ : ℝ} (hmoment : ∀ w, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (ρ ^ 2))
    (w : Vec d) : ‖∫ z, g w z ∂D‖ ≤ 1 + ρ ^ 2 := by
  have hgw : Measurable (g w) := hg.of_uncurry_left
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    hgw.norm.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ z, ENNReal.ofReal ‖g w z‖ ∂D
      ≤ ∫⁻ z, (1 + ENNReal.ofReal (‖g w z‖ ^ 2)) ∂D := by
        refine lintegral_mono fun z => ?_
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (g w z)])
    _ = 1 + ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal (ρ ^ 2) := by gcongr; exact hmoment w
    _ = ENNReal.ofReal (1 + ρ ^ 2) := by
        rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]

/-- A strongly convex function on `ℝ^d`, `d ≥ 1`, cannot have uniformly bounded subgradients
everywhere. -/
lemma strongConvex_bounded_subgradients_false {d : ℕ} (hd : 0 < d) (f : Vec d → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (hf : StrongConvexOn Set.univ lam f) (s : Vec d → Vec d) {M : ℝ}
    (hs : ∀ w, IsSubgradient f w (s w)) (hM : ∀ w, ‖s w‖ ≤ M) : False := by
  set e : Vec d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by simp [he]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set R : ℝ := 8 * M / lam + 1 with hR
  have hRpos : 0 < R := by positivity
  have hconv := hf.2 (Set.mem_univ (0 : Vec d)) (Set.mem_univ (R • e))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hp : (1 / 2 : ℝ) • (0 : Vec d) + (1 / 2 : ℝ) • (R • e) = (R / 2) • e := by
    rw [smul_zero, zero_add, smul_smul]; ring_nf
  rw [hp] at hconv
  have hnorm1 : ‖(0 : Vec d) - R • e‖ = R := by
    rw [zero_sub, norm_neg, norm_smul, hen, Real.norm_eq_abs, abs_of_pos hRpos, mul_one]
  rw [hnorm1] at hconv
  -- subgradient at `0`, tested at `(R/2) e`
  have h0 := hs 0 ((R / 2) • e)
  have hi0 : |⟪(R / 2) • e - 0, s 0⟫_ℝ| ≤ ‖(R / 2) • e - 0‖ * ‖s 0‖ :=
    abs_real_inner_le_norm _ _
  have hn0 : ‖(R / 2) • e - 0‖ = R / 2 := by
    rw [sub_zero, norm_smul, hen, Real.norm_eq_abs, abs_of_pos (by positivity), mul_one]
  rw [hn0] at hi0
  -- subgradient at `R e`, tested at `0`
  have h1 := hs (R • e) 0
  have hi1 : |⟪0 - R • e, s (R • e)⟫_ℝ| ≤ ‖0 - R • e‖ * ‖s (R • e)‖ :=
    abs_real_inner_le_norm _ _
  rw [hnorm1] at hi1
  have hM1 := hM 0
  have hM2 := hM (R • e)
  have a1 := neg_abs_le ⟪(R / 2) • e - 0, s 0⟫_ℝ
  have a2 := neg_abs_le ⟪0 - R • e, s (R • e)⟫_ℝ
  have b1 : R / 2 * ‖s 0‖ ≤ R / 2 * M := by gcongr
  have b2 : R * ‖s (R • e)‖ ≤ R * M := by gcongr
  simp only [smul_eq_mul] at hconv
  -- combine: `lam R² / 8 ≤ M R`
  have key : lam * R ^ 2 / 8 ≤ M * R := by nlinarith
  have : lam * R / 8 ≤ M := by
    have := key; rw [pow_two] at this
    nlinarith
  have : R ≤ 8 * M / lam := by
    rw [le_div_iff₀ hlam]; linarith
  linarith

theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (f : Vec d → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (hf : StrongConvexOn Set.univ lam f) (H : Set (Vec d)) (hH : Convex ℝ H)
    (hclosed : IsClosed H) (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : IsSubgradientOracle f D g) {ρ : ℝ}
    (hmoment : ∀ w, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (ρ ^ 2))
    (wstar : Vec d) (hw : wstar ∈ H) (T : ℕ) (hT : 0 < T) :
    (∫ S, f (sgdStrongAverage lam H g S) ∂(iidLaw D T)) - f wstar ≤
      ρ ^ 2 / (2 * lam * T) * (1 + Real.log T) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hsub : ∀ x y : Vec 0, x = y := fun x y => by ext i; exact i.elim0
    have : IsProbabilityMeasure (iidLaw D T) := by
      unfold iidLaw; infer_instance
    have hconst : (fun S : Fin T → Z => f (sgdStrongAverage lam H g S)) = fun _ => f wstar := by
      funext S; rw [hsub (sgdStrongAverage lam H g S) wstar]
    rw [hconst, integral_const, probReal_univ, one_smul, sub_self]
    have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have := Real.log_nonneg hTr
    positivity
  · exfalso
    exact strongConvex_bounded_subgradients_false hd f hlam hf (fun w => ∫ z, g w z ∂D)
      horacle (norm_integral_le_of_moment D g hg hmoment)
