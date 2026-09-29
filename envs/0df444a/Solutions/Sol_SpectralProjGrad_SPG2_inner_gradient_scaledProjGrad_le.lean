-- Prove2me | solution 1 for SpectralProjGrad.SPG2.inner_gradient_scaledProjGrad_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:10:04.735551+00:00
-- url     : https://prove2.me/submissions/8558c6c7-eac5-45e1-9102-f62768b44ac6

import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_SPG2_IsSPG2Run
import Definitions.Def_SpectralProjGrad_Shared_IsConstrainedStationary
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad
import Mathlib

open Filter Topology

namespace SpectralProjGrad.SPG2

open SpectralProjGrad.Shared

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma limit_le {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => B + t * C) (𝓝[>] 0) (𝓝 (B + 0 * C)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htt
  exact h t htt.1 htt.2.le

/-- Variational inequality for the projection onto a convex set. -/
lemma proj_vi {Ω : Set E} {P : E → E} (hΩ : Convex ℝ Ω) (hP : IsProjOnto Ω P) (z y : E)
    (hy : y ∈ Ω) : inner ℝ (z - P z) (y - P z) ≤ 0 := by
  obtain ⟨hPz, hmin⟩ := hP z
  have key : 2 * inner ℝ (z - P z) (y - P z) ≤ 0 := by
    apply limit_le (C := ‖y - P z‖ ^ 2)
    intro t ht0 ht1
    have hmem : P z + t • (y - P z) ∈ Ω := by
      have := hΩ hPz hy (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1; module
    have h := hmin _ hmem
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    have e : z - (P z + t • (y - P z)) = (z - P z) - t • (y - P z) := by abel
    rw [e, norm_sub_sq_real (z - P z) (t • (y - P z)), norm_smul, real_inner_smul_right,
      Real.norm_eq_abs, abs_of_pos ht0] at hsq
    have : t * (2 * inner ℝ (z - P z) (y - P z)) ≤ t * (0 + t * ‖y - P z‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  linarith

lemma inner_scaled_le {Ω : Set E} {P : E → E} {f : E → ℝ} (hΩ : Convex ℝ Ω)
    (hP : IsProjOnto Ω P) (t : ℝ) (ht : 0 < t) (x : E) (hx : x ∈ Ω) :
    inner ℝ (gradient f x) (scaledProjGrad P f t x) ≤ -(1 / t) * ‖scaledProjGrad P f t x‖ ^ 2 := by
  have h := proj_vi hΩ hP (x - t • gradient f x) x hx
  set d := scaledProjGrad P f t x with hd
  have e1 : x - t • gradient f x - P (x - t • gradient f x) = -(d + t • gradient f x) := by
    rw [hd, scaledProjGrad]; abel
  have e2 : x - P (x - t • gradient f x) = -d := by rw [hd, scaledProjGrad]; abel
  rw [e1, e2, inner_neg_left, inner_neg_right, neg_neg, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h
  rw [show -(1 / t) * ‖d‖ ^ 2 = (-‖d‖ ^ 2) / t by ring, le_div_iff₀ ht]
  linarith

lemma scaled_zero_iff {Ω : Set E} {P : E → E} {f : E → ℝ} (hΩ : Convex ℝ Ω)
    (hP : IsProjOnto Ω P) (t : ℝ) (ht : 0 < t) (xbar : E) (hxbar : xbar ∈ Ω) :
    scaledProjGrad P f t xbar = 0 ↔ IsConstrainedStationary Ω f xbar := by
  constructor
  · intro h x hx
    have hP0 : P (xbar - t • gradient f xbar) = xbar := by
      rw [scaledProjGrad, sub_eq_zero] at h; exact h
    have v := proj_vi hΩ hP (xbar - t • gradient f xbar) x hx
    rw [hP0, show xbar - t • gradient f xbar - xbar = -(t • gradient f xbar) by abel,
      inner_neg_left, real_inner_smul_left] at v
    have : 0 ≤ t * inner ℝ (gradient f xbar) (x - xbar) := by linarith
    exact (mul_nonneg_iff_of_pos_left ht).1 this
  · intro hst
    set z := xbar - t • gradient f xbar with hz
    obtain ⟨hPz, hmin⟩ := hP z
    have h1 := hmin xbar hxbar
    have h2 : ‖z - xbar‖ ^ 2 + ‖xbar - P z‖ ^ 2 ≤ ‖z - P z‖ ^ 2 := by
      have e : z - P z = (z - xbar) + (xbar - P z) := by abel
      rw [e, norm_add_sq_real]
      have hzx : z - xbar = -(t • gradient f xbar) := by rw [hz]; abel
      rw [hzx, inner_neg_left, real_inner_smul_left]
      have := hst (P z) hPz
      have e2 : xbar - P z = -(P z - xbar) := by abel
      rw [e2, inner_neg_right]
      nlinarith
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have : ‖xbar - P z‖ ^ 2 ≤ 0 := by linarith
    have hn : ‖xbar - P z‖ = 0 := by nlinarith [norm_nonneg (xbar - P z)]
    rw [norm_eq_zero, sub_eq_zero] at hn
    rw [scaledProjGrad, ← hz, ← hn, sub_self]

theorem scaledProjGrad_eq_zero_iff_stationary {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (t : ℝ) (ht : t ∈ Set.Ioc 0 αmax)
    (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : xbar ∈ Ω) :
    SpectralProjGrad.Shared.scaledProjGrad P f t xbar = 0 ↔ SpectralProjGrad.Shared.IsConstrainedStationary Ω f xbar :=
  scaled_zero_iff hΩ_convex hP t ht.1 xbar hxbar

theorem inner_gradient_scaledProjGrad_le {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (t : ℝ) (ht : t ∈ Set.Ioc 0 αmax)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    inner ℝ (gradient f x) (SpectralProjGrad.Shared.scaledProjGrad P f t x) ≤ -(1 / t) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 ∧
      -(1 / t) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 ≤ -(1 / αmax) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 := by
  refine ⟨inner_scaled_le hΩ_convex hP t ht.1 x hx, ?_⟩
  have h1 : 1 / αmax ≤ 1 / t := one_div_le_one_div_of_le ht.1 ht.2
  have := sq_nonneg ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖
  nlinarith

/-- Derivative of `f` along a line at a point of differentiability. -/
lemma line_deriv0 (f : E → ℝ) (x d : E) (hfx : DifferentiableAt ℝ f x) :
    HasDerivAt (fun μ : ℝ => f (x + μ • d)) (inner ℝ (gradient f x) d) 0 := by
  have hl : HasDerivAt (fun μ : ℝ => x + μ • d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
  have hf : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • d) := by
    rw [zero_smul, add_zero]; exact hfx.hasFDerivAt
  have := hf.comp_hasDerivAt (0:ℝ) hl
  have e : fderiv ℝ f x d = inner ℝ (gradient f x) d := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this

theorem backtracking_terminates {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax γ σ₁ σ₂ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (hstep1 : ‖P (x - gradient f x) - x‖ ≠ 0)
    (α : ℝ) (hα : α ∈ Set.Icc αmin αmax)
    (R : ℝ) (hR : f x ≤ R)
    (μ : ℕ → ℝ) (hμ0 : μ 0 = 1)
    (hμ : ∀ i, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) :
    ∃ i, f (x + μ i • SpectralProjGrad.Shared.scaledProjGrad P f α x) ≤
      R + γ * μ i * inner ℝ (SpectralProjGrad.Shared.scaledProjGrad P f α x) (gradient f x) := by
  have hα0 : 0 < α := lt_of_lt_of_le hαmin hα.1
  set d := scaledProjGrad P f α x with hd
  -- d ≠ 0
  have hd0 : d ≠ 0 := by
    intro h0
    have hst := (scaled_zero_iff hΩ_convex hP α hα0 x hx).1 h0
    have h1 := (scaled_zero_iff (f := f) hΩ_convex hP 1 one_pos x hx).2 hst
    apply hstep1
    rw [scaledProjGrad, one_smul] at h1
    rw [h1, norm_zero]
  have hneg : inner ℝ (gradient f x) d < 0 := by
    have h := inner_scaled_le (f := f) hΩ_convex hP α hα0 x hx
    have hpos : 0 < ‖d‖ ^ 2 := by positivity
    have : 0 < 1 / α * ‖d‖ ^ 2 := by positivity
    linarith
  -- differentiability
  have hfx : DifferentiableAt ℝ f x :=
    ((hf.differentiableOn (by norm_num)) x (hΩU hx)).differentiableAt (hU_open.mem_nhds (hΩU hx))
  have hder := (line_deriv0 f x d hfx).tendsto_slope_zero_right
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hder
  -- eventually the slope is below γ ⟪g, d⟫
  have hγ1 : inner ℝ (gradient f x) d < γ * inner ℝ (gradient f x) d := by
    nlinarith [hγ.2]
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ * (f (x + t • d) - f x) < γ * inner ℝ (gradient f x) d :=
    hder.eventually (gt_mem_nhds hγ1)
  -- μ i → 0⁺
  have hμpos : ∀ i, 0 < μ i := by
    intro i; induction i with
    | zero => rw [hμ0]; norm_num
    | succ i ih => exact lt_of_lt_of_le (mul_pos hσ₁ ih) (hμ i).1
  have hμle : ∀ i, μ i ≤ σ₂ ^ i := by
    intro i; induction i with
    | zero => rw [hμ0]; simp
    | succ i ih =>
      calc μ (i + 1) ≤ σ₂ * μ i := (hμ i).2
        _ ≤ σ₂ * σ₂ ^ i := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = σ₂ ^ (i + 1) := by ring
  have hμlim : Tendsto μ atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, Eventually.of_forall (fun i => hμpos i)⟩
    have hpow : Tendsto (fun i : ℕ => σ₂ ^ i) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) hσ₂
    exact squeeze_zero (fun i => (hμpos i).le) hμle hpow
  obtain ⟨i, hi⟩ := (hμlim.eventually hev).exists
  refine ⟨i, ?_⟩
  have hmi := hμpos i
  rw [inv_mul_lt_iff₀ hmi] at hi
  rw [real_inner_comm]
  nlinarith

lemma spectral_mem (αmin αmax : ℝ) (h : αmin < αmax) (s y : E) :
    spectralStep αmin αmax s y ∈ Set.Icc αmin αmax := by
  unfold spectralStep
  split_ifs
  · exact ⟨h.le, le_rfl⟩
  · exact ⟨le_min h.le (le_max_left _ _), min_le_left _ _⟩

theorem iterates_mem_levelSet {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {M : ℕ} {αmin αmax γ σ₁ σ₂ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hM : 1 ≤ M) (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ < 1)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ}
    (hrun : IsSPG2Run Ω f P M αmin αmax γ σ₁ σ₂ x α) :
    ∀ k, x k ∈ {y ∈ Ω | f y ≤ f (x 0)} := by
  have hαk : ∀ k, α k ∈ Set.Icc αmin αmax := by
    intro k; cases k with
    | zero => exact hrun.start_step
    | succ k => rw [hrun.step3_spectral k]; exact spectral_mem αmin αmax hαmin_lt _ _
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · exact ⟨hrun.start_mem, le_rfl⟩
    · obtain ⟨hxk, _⟩ := ih k (Nat.lt_succ_self k)
      obtain ⟨m, μ, hμ0, hμ, _, htest, hnext⟩ := hrun.step2_backtrack k
      have hα0 : 0 < α k := lt_of_lt_of_le hαmin (hαk k).1
      -- step length in [0, 1]
      have hμpos : ∀ i ≤ m, 0 < μ i := by
        intro i hi
        induction i with
        | zero => rw [hμ0]; norm_num
        | succ i ihi => exact lt_of_lt_of_le (mul_pos hσ₁ (ihi (by omega))) (hμ i (by omega)).1
      have hμle : ∀ i ≤ m, μ i ≤ 1 := by
        intro i hi
        induction i with
        | zero => rw [hμ0]
        | succ i ihi =>
          have h1 := (hμ i (by omega)).2
          have h2 := ihi (by omega)
          have h3 := hμpos i (by omega)
          nlinarith
      have hm0 := hμpos m le_rfl
      have hm1 := hμle m le_rfl
      set d := scaledProjGrad P f (α k) (x k) with hd
      have hmem : x (k + 1) ∈ Ω := by
        rw [hnext]
        have hPm : P (x k - α k • gradient f (x k)) ∈ Ω := (hP _).1
        have := hΩ_convex hxk hPm (by linarith : (0:ℝ) ≤ 1 - μ m) hm0.le (by ring)
        convert this using 1
        rw [hd, scaledProjGrad]; module
      refine ⟨hmem, ?_⟩
      have hinner : inner ℝ d (gradient f (x k)) ≤ 0 := by
        have h := inner_scaled_le (f := f) hΩ_convex hP (α k) hα0 (x k) hxk
        rw [real_inner_comm]
        have : 0 ≤ 1 / α k * ‖d‖ ^ 2 := by positivity
        linarith
      have href : nonmonotoneRef f x M k ≤ f (x 0) := by
        unfold nonmonotoneRef
        apply Finset.sup'_le
        intro j hj
        rw [Finset.mem_range] at hj
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0; simp only [Nat.sub_zero]; exact (ih k (Nat.lt_succ_self k)).2
        · exact (ih (k - j) (by omega)).2
      have := htest
      unfold SPG2Test at this
      rw [← hnext] at this
      have hγ0 : 0 ≤ γ * μ m := mul_nonneg hγ.1.le hm0.le
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hγ0 hinner]

end SpectralProjGrad.SPG2

open SpectralProjGrad.SPG2

theorem solution {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (t : ℝ) (ht : t ∈ Set.Ioc 0 αmax)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    inner ℝ (gradient f x) (SpectralProjGrad.Shared.scaledProjGrad P f t x) ≤ -(1 / t) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 ∧
      -(1 / t) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 ≤ -(1 / αmax) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 := by
  exact inner_gradient_scaledProjGrad_le hΩ_closed hΩ_convex hU_open hΩU hf hP hαmin hαmin_lt t ht x hx
