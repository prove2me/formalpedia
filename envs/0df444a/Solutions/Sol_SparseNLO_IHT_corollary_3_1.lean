-- Prove2me | solution 1 for SparseNLO.IHT.corollary_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:18:20.330513+00:00
-- url     : https://prove2.me/submissions/17b054eb-2c44-4894-9d27-a8fda62054ea

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

set_option autoImplicit false
open Filter Topology SparseNLO.IHT

theorem sih_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (hf : Differentiable ℝ f) (Lf : NNReal) (hLip : LipschitzWith Lf (gradient f))
    (x y : E) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + (Lf : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  set d : E := y - x with hd
  have hgrad : ∀ p w : E, fderiv ℝ f p w = inner ℝ (gradient f p) w := by
    intro p w
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hphi : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • d)) (inner ℝ (gradient f (x + t • d)) d) t := by
    intro t
    have := (hf (x + t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [hgrad] at this
    exact this
  set ψ : ℝ → ℝ := fun t => f (x + t • d) - f x - t * inner ℝ (gradient f x) d
    - (Lf : ℝ) / 2 * ‖d‖ ^ 2 * t ^ 2 with hψ
  have hψd : ∀ t : ℝ, HasDerivAt ψ (inner ℝ (gradient f (x + t • d)) d - inner ℝ (gradient f x) d
      - (Lf : ℝ) * ‖d‖ ^ 2 * t) t := by
    intro t
    have h1 := ((hphi t).sub_const (f x)).sub ((hasDerivAt_id t).mul_const (inner ℝ (gradient f x) d))
    have h2 := h1.sub ((hasDerivAt_pow 2 t).const_mul ((Lf : ℝ) / 2 * ‖d‖ ^ 2))
    exact h2.congr_deriv (by norm_num; ring)
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hcs : inner ℝ (gradient f (x + t • d) - gradient f x) d ≤ ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ :=
        real_inner_le_norm _ _
      have hL : ‖gradient f (x + t • d) - gradient f x‖ ≤ Lf * (t * ‖d‖) := by
        have := hLip.dist_le_mul (x + t • d) x
        rw [dist_eq_norm, dist_eq_norm] at this
        simpa [norm_smul, abs_of_pos ht.1] using this
      rw [inner_sub_left] at hcs
      have : ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ ≤ Lf * (t * ‖d‖) * ‖d‖ := by gcongr
      nlinarith
  have h01 := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [hψ] at h01
  have hy : x + (1 : ℝ) • d = y := by simp [hd]
  simp only [hy, zero_smul, add_zero, zero_mul, sub_zero, one_mul, one_pow, mul_one, sub_self] at h01
  have : ‖y - x‖ = ‖d‖ := rfl
  linarith

theorem sih_proj {n s : ℕ} (g x y : EuclideanSpace ℝ (Fin n)) (L : ℝ) (hL : 0 < L)
    (hx : x ∈ SparseNLO.CWOpt.Cs n s) (hy : y ∈ projCs n s (x - (1 / L) • g)) :
    inner ℝ g (y - x) ≤ -(L / 2) * ‖y - x‖ ^ 2 := by
  have h := hy.2 x hx
  have h2 : ‖y - (x - (1 / L) • g)‖ ^ 2 ≤ ‖x - (x - (1 / L) • g)‖ ^ 2 := by gcongr
  have e1 : y - (x - (1 / L) • g) = (y - x) + (1 / L) • g := by abel
  have e2 : x - (x - (1 / L) • g) = (1 / L) • g := by abel
  rw [e1, e2, norm_add_sq_real, norm_smul, real_inner_smul_right, real_inner_comm] at h2
  have hL' : 0 < 1 / L := by positivity
  rw [Real.norm_eq_abs, abs_of_pos hL'] at h2
  have h3 : 2 * (1 / L) * inner ℝ g (y - x) ≤ -‖y - x‖ ^ 2 := by nlinarith
  have h4 : inner ℝ g (y - x) ≤ -(L / 2) * ‖y - x‖ ^ 2 := by
    have : 2 * (1 / L) * inner ℝ g (y - x) * (L / 2) ≤ -‖y - x‖ ^ 2 * (L / 2) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have e3 : 2 * (1 / L) * inner ℝ g (y - x) * (L / 2) = inner ℝ g (y - x) := by
      field_simp
    linarith
  exact h4

theorem sih_lemma24 {n s : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (Lf : NNReal) (hLip : LipschitzWith Lf (gradient f)) (L : ℝ) (hL : (Lf : ℝ) < L)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ SparseNLO.CWOpt.Cs n s)
    (hy : y ∈ projCs n s (x - (1 / L) • gradient f x)) :
    f x - f y ≥ (L - Lf) / 2 * ‖x - y‖ ^ 2 := by
  have hL0 : 0 < L := lt_of_le_of_lt (NNReal.coe_nonneg Lf) hL
  have hd := sih_descent f (hf.differentiable one_ne_zero) Lf hLip x y
  have hp := sih_proj (gradient f x) x y L hL0 hx hy
  have : ‖x - y‖ = ‖y - x‖ := norm_sub_rev _ _
  rw [this]
  nlinarith


theorem sih_run_mem {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsIHTRun f s L x) :
    ∀ k, x k ∈ SparseNLO.CWOpt.Cs n s := by
  intro k
  cases k with
  | zero => exact hx.1
  | succ k => exact (hx.2 k).1

theorem sih_lemma31 {n s : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (Lf : NNReal) (hLip : LipschitzWith Lf (gradient f)) (L : ℝ) (hL : (Lf : ℝ) < L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsIHTRun f s L x) :
    (∀ k : ℕ, f (x k) - f (x (k + 1)) ≥ (L - Lf) / 2 * ‖x k - x (k + 1)‖ ^ 2) ∧
    Antitone (fun k => f (x k)) ∧
    Tendsto (fun k => ‖x k - x (k + 1)‖) atTop (𝓝 0) ∧
    (∀ k : ℕ, x k ≠ x (k + 1) → f (x (k + 1)) < f (x k)) := by
  have h1 : ∀ k : ℕ, f (x k) - f (x (k + 1)) ≥ (L - Lf) / 2 * ‖x k - x (k + 1)‖ ^ 2 :=
    fun k => sih_lemma24 f hf Lf hLip L hL (x k) (x (k + 1)) (sih_run_mem f L x hx k) (hx.2 k)
  have hc : 0 < (L - Lf) / 2 := by linarith
  refine ⟨h1, ?_, ?_, ?_⟩
  · refine antitone_nat_of_succ_le fun k => ?_
    have := h1 k
    have : 0 ≤ (L - Lf) / 2 * ‖x k - x (k + 1)‖ ^ 2 := by positivity
    show f (x (k + 1)) ≤ f (x k)
    linarith [h1 k]
  · obtain ⟨γ, hγ⟩ := hbdd
    have hsum : ∀ N : ℕ, ∑ k ∈ Finset.range N, ‖x k - x (k + 1)‖ ^ 2 ≤ (f (x 0) - γ) / ((L - Lf) / 2) := by
      intro N
      rw [le_div_iff₀ hc]
      have : ∑ k ∈ Finset.range N, (L - Lf) / 2 * ‖x k - x (k + 1)‖ ^ 2
          ≤ ∑ k ∈ Finset.range N, (f (x k) - f (x (k + 1))) := Finset.sum_le_sum fun k _ => h1 k
      rw [Finset.sum_range_sub'] at this
      rw [← Finset.mul_sum] at this
      have := hγ (x N)
      nlinarith
    have hs : Summable fun k => ‖x k - x (k + 1)‖ ^ 2 :=
      summable_of_sum_range_le (fun k => by positivity) hsum
    have ht := hs.tendsto_atTop_zero
    have := (Real.continuous_sqrt.tendsto 0).comp ht
    simp only [Real.sqrt_zero] at this
    refine this.congr fun k => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  · intro k hk
    have hpos : 0 < ‖x k - x (k + 1)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hk)
    have : 0 < (L - Lf) / 2 * ‖x k - x (k + 1)‖ ^ 2 := by positivity
    linarith [h1 k]

theorem solution {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (Lf : NNReal) (hLip : LipschitzWith Lf (gradient f)) (L : ℝ) (hL : (Lf : ℝ) < L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsIHTRun f s L x) :
    ∃ c : ℝ, Tendsto (fun k => f (x k)) atTop (𝓝 c) := by
  obtain ⟨_, hanti, _, _⟩ := sih_lemma31 f hf hbdd Lf hLip L hL x hx
  obtain ⟨γ, hγ⟩ := hbdd
  have hb : BddBelow (Set.range fun k => f (x k)) := ⟨γ, by rintro _ ⟨k, rfl⟩; exact hγ _⟩
  exact ⟨_, tendsto_atTop_ciInf hanti hb⟩
