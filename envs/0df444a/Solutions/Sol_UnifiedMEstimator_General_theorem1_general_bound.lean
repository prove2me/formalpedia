-- Prove2me | solution 1 for UnifiedMEstimator.General.theorem1_general_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:09:32.810225+00:00
-- url     : https://prove2.me/submissions/b1f7c9dd-0939-4c01-883d-bc14f1793556

import Mathlib
import Definitions.Def_UnifiedMEstimator_General_Core

set_option autoImplicit false

open UnifiedMEstimator.General in
theorem p2me7bcd_upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R : E → ℝ) (hR : IsNormFn R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, R x ≤ C * ‖x‖ := by
  let b := stdOrthonormalBasis ℝ E
  refine ⟨∑ i, R (b i), Finset.sum_nonneg (fun i _ => hR.nonneg _), fun x => ?_⟩
  have h0 : R 0 = 0 := (hR.eq_zero_iff 0).2 rfl
  calc R x = R (∑ i, inner ℝ (b i) x • b i) := by rw [b.sum_repr']
    _ ≤ ∑ i, R (inner ℝ (b i) x • b i) :=
        Finset.le_sum_of_subadditive R h0.le hR.triangle _ _
    _ = ∑ i, |inner ℝ (b i) x| * R (b i) := by
        apply Finset.sum_congr rfl; intro i _; exact hR.smul_abs _ _
    _ ≤ ∑ i, ‖x‖ * R (b i) := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_right _ (hR.nonneg _)
        calc |inner ℝ (b i) x| ≤ ‖b i‖ * ‖x‖ := abs_real_inner_le_norm _ _
          _ = ‖x‖ := by rw [b.orthonormal.1 i, one_mul]
    _ = (∑ i, R (b i)) * ‖x‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

open UnifiedMEstimator.General in
theorem p2me7bcd_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R : E → ℝ) (hR : IsNormFn R) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ R x := by
  obtain ⟨C, hC0, hC⟩ := p2me7bcd_upper R hR
  have h0 : R 0 = 0 := (hR.eq_zero_iff 0).2 rfl
  have hneg : ∀ x, R (-x) = R x := fun x => by
    have := hR.smul_abs (-1) x; simpa using this
  have hcont : Continuous R := by
    have hL : LipschitzWith ⟨C, hC0⟩ R := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, dist_eq_norm]
      change |R x - R y| ≤ C * ‖x - y‖
      have h1 : R x ≤ R (x - y) + R y := by
        have := hR.triangle (x - y) y; simpa using this
      have h2 : R y ≤ R (y - x) + R x := by
        have := hR.triangle (y - x) x; simpa using this
      have h3 : R (y - x) = R (x - y) := by rw [← neg_sub, hneg]
      have h4 := hC (x - y)
      rw [abs_le]; constructor <;> linarith
    exact hL.continuous
  by_cases hE : (Metric.sphere (0:E) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ :=
      (isCompact_sphere (0:E) 1).exists_isMinOn hE hcont.continuousOn
    have hx0n : ‖x0‖ = 1 := by simpa using hx0
    have hx0ne : x0 ≠ 0 := by
      intro h; rw [h, norm_zero] at hx0n; exact zero_ne_one hx0n
    have hc : 0 < R x0 :=
      lt_of_le_of_ne (hR.nonneg _) (fun h => hx0ne ((hR.eq_zero_iff x0).1 h.symm))
    refine ⟨R x0, hc, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [h0]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0:E) 1 := by
        simp [norm_smul, hxn.ne']
      have := isMinOn_iff.1 hmin _ hy
      rw [hR.smul_abs, abs_of_pos (inv_pos.2 hxn), le_inv_mul_iff₀ hxn] at this
      linarith [mul_comm (R x0) ‖x‖]
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [h0]
    · exfalso; apply hE
      exact ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.2 hx]⟩

open UnifiedMEstimator.General in
theorem p2me7bcd_gcs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R : E → ℝ) (hR : IsNormFn R) (u v : E) :
    inner ℝ u v ≤ R u * dualNorm R v := by
  have h0 : R 0 = 0 := (hR.eq_zero_iff 0).2 rfl
  by_cases hu : u = 0
  · subst hu; simp [h0]
  · have hRu : 0 < R u :=
      lt_of_le_of_ne (hR.nonneg _) (fun h => hu ((hR.eq_zero_iff u).1 h.symm))
    obtain ⟨c, hc, hcR⟩ := p2me7bcd_lower R hR
    have hbdd : BddAbove {r : ℝ | ∃ u : E, R u ≤ 1 ∧ r = inner ℝ u v} := by
      refine ⟨‖v‖ / c, ?_⟩
      rintro r ⟨w, hw, rfl⟩
      have h2 : ‖w‖ ≤ 1 / c := by
        rw [le_div_iff₀ hc]; linarith [hcR w, mul_comm c ‖w‖]
      calc inner ℝ w v ≤ ‖w‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ 1 / c * ‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖v‖ / c := by ring
    have hmem : inner ℝ ((R u)⁻¹ • u) v ∈ {r : ℝ | ∃ u : E, R u ≤ 1 ∧ r = inner ℝ u v} := by
      refine ⟨(R u)⁻¹ • u, ?_, rfl⟩
      rw [hR.smul_abs, abs_of_pos (inv_pos.2 hRu), inv_mul_cancel₀ hRu.ne']
    have := le_csSup hbdd hmem
    rw [real_inner_smul_left, inv_mul_le_iff₀ hRu] at this
    exact this

open UnifiedMEstimator.General in
theorem p2me7bcd_compat {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R : E → ℝ) (hR : IsNormFn R) (S : Submodule ℝ E)
    (u : E) (hu : u ∈ S) : R u ≤ compat R S * ‖u‖ := by
  have h0 : R 0 = 0 := (hR.eq_zero_iff 0).2 rfl
  by_cases hz : u = 0
  · subst hz; simp [h0]
  · obtain ⟨C, hC0, hC⟩ := p2me7bcd_upper R hR
    have hn : 0 < ‖u‖ := norm_pos_iff.2 hz
    have hbdd : BddAbove {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = R u / ‖u‖} := by
      refine ⟨C, ?_⟩
      rintro r ⟨w, -, hw, rfl⟩
      rw [div_le_iff₀ (norm_pos_iff.2 hw)]; exact hC w
    have := le_csSup hbdd ⟨u, hu, hz, rfl⟩
    unfold compat
    rwa [div_le_iff₀ hn] at this

open UnifiedMEstimator.General in
theorem p2me7bcd_compat_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R : E → ℝ) (hR : IsNormFn R) (S : Submodule ℝ E) :
    0 ≤ compat R S := by
  unfold compat
  apply Real.sSup_nonneg
  rintro r ⟨w, -, -, rfl⟩
  exact div_nonneg (hR.nonneg _) (norm_nonneg _)

theorem p2me7bcd_convex_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E → ℝ) (hconv : ConvexOn ℝ Set.univ L)
    (hdiff : Differentiable ℝ L) (θ Δ : E) :
    inner ℝ (gradient L θ) Δ ≤ L (θ + Δ) - L θ := by
  let φ : ℝ → ℝ := fun t => L (θ + t • Δ)
  have hφc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have := hconv.2 (Set.mem_univ (θ + x • Δ)) (Set.mem_univ (θ + y • Δ)) ha hb hab
    have e : a • (θ + x • Δ) + b • (θ + y • Δ) = θ + (a * x + b * y) • Δ := by
      linear_combination (norm := module) hab • θ
    show L (θ + (a • x + b • y) • Δ) ≤ a • L (θ + x • Δ) + b • L (θ + y • Δ)
    rw [smul_eq_mul a x, smul_eq_mul b y, ← e]
    exact this
  have hline : HasDerivAt (fun t : ℝ => θ + t • Δ) Δ 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const Δ).const_add θ
    simpa using this
  have hd : HasDerivAt φ (fderiv ℝ L θ Δ) 0 :=
    (hdiff θ).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hs := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  have hg : inner ℝ (gradient L θ) Δ = fderiv ℝ L θ Δ := by
    simp [gradient]
  rw [hg]
  simpa [slope_def_field, φ] using hs

open UnifiedMEstimator.General in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L R : E → ℝ) (M Mbar : Submodule ℝ E) (θstar θhat : E) (lam κ τ : ℝ)
    (hR : IsNormFn R) (hdec : IsDecomposable R M Mbar)
    (hconv : ConvexOn ℝ Set.univ L) (hdiff : Differentiable ℝ L)
    (hRSC : RSC L R M Mbar θstar κ τ)
    (hlam : 0 < lam) (hlam_dual : 2 * dualNorm R (gradient L θstar) ≤ lam)
    (hopt : IsOptimal L R lam θhat) :
    ‖θhat - θstar‖ ^ 2 ≤ 9 * lam ^ 2 / κ ^ 2 * compat R Mbar ^ 2
        + (2 * τ ^ 2 + 4 * lam * R (Mᗮ.starProjection θstar)) / κ := by
  obtain ⟨hκ, hrsc⟩ := hRSC
  obtain ⟨_hMM, hdecomp⟩ := hdec
  have hneg : ∀ x, R (-x) = R x := fun x => by
    have := hR.smul_abs (-1) x; simpa using this
  set Δ := θhat - θstar with hΔ
  have hθhat : θhat = θstar + Δ := by rw [hΔ]; abel
  set g := gradient L θstar with hg
  have hΔsplit : Δ = Mbar.starProjection Δ + Mbarᗮ.starProjection Δ :=
    (Mbar.starProjection_add_starProjection_orthogonal Δ).symm
  have hθsplit : θstar = M.starProjection θstar + Mᗮ.starProjection θstar :=
    (M.starProjection_add_starProjection_orthogonal θstar).symm
  set Δ1 := Mbar.starProjection Δ with hΔ1
  set Δ2 := Mbarᗮ.starProjection Δ with hΔ2
  set t1 := M.starProjection θstar with ht1
  set t2 := Mᗮ.starProjection θstar with ht2
  -- basic inequality
  have hbasic := hopt θstar
  rw [hθhat] at hbasic
  -- generalized Cauchy-Schwarz with the dual norm
  have hgcs : -(inner ℝ g Δ) ≤ R Δ * (lam / 2) := by
    have h1 := p2me7bcd_gcs R hR (-Δ) g
    rw [inner_neg_left, hneg, real_inner_comm] at h1
    have h2 := mul_le_mul_of_nonneg_left
      (show dualNorm R g ≤ lam / 2 by linarith) (hR.nonneg Δ)
    linarith
  -- decomposability
  have hRΔ : R Δ ≤ R Δ1 + R Δ2 := by
    have := hR.triangle Δ1 Δ2; rwa [← hΔsplit] at this
  have hRθ : R θstar ≤ R t1 + R t2 := by
    have := hR.triangle t1 t2; rwa [← hθsplit] at this
  have hdecR : R Δ2 - R Δ1 - 2 * R t2 ≤ R (θstar + Δ) - R θstar := by
    have ht1m : t1 ∈ M := M.starProjection_apply_mem θstar
    have hΔ2m : Δ2 ∈ Mbarᗮ := Mbarᗮ.starProjection_apply_mem Δ
    have e1 := hdecomp t1 ht1m Δ2 hΔ2m
    have e2 : t1 + Δ2 = (θstar + Δ) + (-(t2 + Δ1)) := by
      rw [hθsplit, hΔsplit]; abel
    have h3 : R (t1 + Δ2) ≤ R (θstar + Δ) + R (t2 + Δ1) := by
      rw [e2]
      calc R (θstar + Δ + -(t2 + Δ1)) ≤ R (θstar + Δ) + R (-(t2 + Δ1)) := hR.triangle _ _
        _ = R (θstar + Δ) + R (t2 + Δ1) := by rw [hneg]
    have h4 := hR.triangle t2 Δ1
    linarith
  -- convexity: first-order condition
  have hcvx : inner ℝ g Δ ≤ L (θstar + Δ) - L θstar :=
    p2me7bcd_convex_grad L hconv hdiff θstar Δ
  have hRΔs : R Δ * (lam / 2) ≤ (R Δ1 + R Δ2) * (lam / 2) :=
    mul_le_mul_of_nonneg_right hRΔ (by positivity)
  have hlamdec : lam * (R Δ2 - R Δ1 - 2 * R t2) ≤ lam * (R (θstar + Δ) - R θstar) :=
    mul_le_mul_of_nonneg_left hdecR hlam.le
  -- Δ lies in the cone C
  have hC : Δ ∈ setC R M Mbar θstar := by
    show R Δ2 ≤ 3 * R Δ1 + 4 * R t2
    by_contra hcon'
    have hcon := not_le.1 hcon'
    have := mul_pos hlam (sub_pos.2 hcon)
    nlinarith
  have hrs := hrsc Δ hC
  unfold taylorErr at hrs
  rw [← hg] at hrs
  -- compatibility
  have hΨ0 : 0 ≤ compat R Mbar := p2me7bcd_compat_nonneg R hR Mbar
  have hΔ1b : R Δ1 ≤ compat R Mbar * ‖Δ‖ := by
    have h1 := p2me7bcd_compat R hR Mbar Δ1 (Mbar.starProjection_apply_mem Δ)
    have h2 : ‖Δ1‖ ≤ ‖Δ‖ := Mbar.norm_starProjection_apply_le Δ
    have h3 := mul_le_mul_of_nonneg_left h2 hΨ0
    linarith
  have hR2 : 0 ≤ R Δ2 := hR.nonneg _
  have hRt2 : 0 ≤ R t2 := hR.nonneg _
  set x := ‖Δ‖ with hx
  set Ψ := compat R Mbar with hΨ
  have hlamΔ1 : lam * R Δ1 ≤ lam * (Ψ * x) := mul_le_mul_of_nonneg_left hΔ1b hlam.le
  have hmain : κ * x ^ 2 - τ ^ 2 ≤ 3 / 2 * (lam * Ψ * x) + 2 * lam * R t2 := by
    nlinarith
  set w := lam * Ψ / κ with hw
  have hlw : lam * Ψ = κ * w := by rw [hw]; field_simp
  rw [hlw] at hmain
  have hkey : κ * x ^ 2 ≤ 2 * τ ^ 2 + 4 * lam * R t2 + 9 * κ * w ^ 2 := by
    nlinarith [mul_nonneg hκ.le (sq_nonneg (x - 3 / 2 * w)), mul_nonneg hκ.le (sq_nonneg w)]
  have e9 : 9 * lam ^ 2 / κ ^ 2 * Ψ ^ 2 = 9 * w ^ 2 := by
    rw [hw]; field_simp
  rw [e9]
  have h5 : x ^ 2 - 9 * w ^ 2 ≤ (2 * τ ^ 2 + 4 * lam * R t2) / κ := by
    rw [le_div_iff₀ hκ]; nlinarith
  linarith
