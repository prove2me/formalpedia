-- Prove2me | solution 1 for ShorNonsmooth.Fejer.polyak_method_converges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T08:52:50.377773+00:00
-- url     : https://prove2.me/submissions/5f348b7b-6f60-4214-b981-56f44bf5438d

import Mathlib
import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

set_option autoImplicit false

open Filter Topology

namespace PolyakAux

/-- The basic Fejer inequality for one Polyak step. -/
lemma step_sq {n : ℕ} (a v : EuclideanSpace ℝ (Fin n)) (δ γ : ℝ) (hδ : 0 < δ)
    (hγ0 : 0 < γ) (hv : v ≠ 0) (hav : δ ≤ inner ℝ v a) :
    ‖a - (γ * δ / ‖v‖ ^ 2) • v‖ ^ 2 + γ * (2 - γ) * (δ ^ 2 / ‖v‖ ^ 2) ≤ ‖a‖ ^ 2 := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ γ * δ / ‖v‖ ^ 2), real_inner_comm]
  have key : 2 * (γ * δ / ‖v‖ ^ 2 * inner ℝ v a) ≥ 2 * (γ * δ / ‖v‖ ^ 2 * δ) := by
    have : 0 ≤ γ * δ / ‖v‖ ^ 2 := by positivity
    nlinarith
  have e1 : (γ * δ / ‖v‖ ^ 2 * ‖v‖) ^ 2 = γ ^ 2 * δ ^ 2 / ‖v‖ ^ 2 := by
    field_simp
  have e2 : 2 * (γ * δ / ‖v‖ ^ 2 * δ) = 2 * γ * δ ^ 2 / ‖v‖ ^ 2 := by
    field_simp
  have e3 : γ * (2 - γ) * (δ ^ 2 / ‖v‖ ^ 2) = 2 * γ * δ ^ 2 / ‖v‖ ^ 2 - γ ^ 2 * δ ^ 2 / ‖v‖ ^ 2 := by
    ring
  rw [e1, e3]
  linarith

/-- Subgradients of a function bounded by `C` on `closedBall y (R+1)` at points of
`closedBall y R` have norm at most `2C`. -/
lemma subgrad_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (y z v : EuclideanSpace ℝ (Fin n))
    (R C : ℝ) (hC : ∀ w ∈ Metric.closedBall y (R + 1), ‖f w‖ ≤ C)
    (hz : z ∈ Metric.closedBall y R) (hv : ShorNonsmooth.AlmostDiff.IsSubgradient f z v) :
    ‖v‖ ≤ 2 * C := by
  have hR : 0 ≤ R := le_trans dist_nonneg hz
  have hzC := hC z (Metric.closedBall_subset_closedBall (by linarith) hz)
  by_cases h0 : v = 0
  · rw [h0, norm_zero]
    have := norm_nonneg (f z)
    linarith
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr h0
  set w := z + (1 / ‖v‖) • v with hw
  have hwB : w ∈ Metric.closedBall y (R + 1) := by
    rw [Metric.mem_closedBall] at hz ⊢
    rw [dist_eq_norm] at hz ⊢
    have : w - y = (z - y) + (1 / ‖v‖) • v := by rw [hw]; abel
    rw [this]
    calc ‖(z - y) + (1 / ‖v‖) • v‖ ≤ ‖z - y‖ + ‖(1 / ‖v‖) • v‖ := norm_add_le _ _
      _ = ‖z - y‖ + 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          field_simp
      _ ≤ R + 1 := by linarith
  have hwC := hC w hwB
  have h1 := hv w
  have : w - z = (1 / ‖v‖) • v := by rw [hw]; abel
  rw [this, inner_smul_right, real_inner_self_eq_norm_sq] at h1
  have h2 : 1 / ‖v‖ * ‖v‖ ^ 2 = ‖v‖ := by field_simp
  rw [h2] at h1
  have a1 := abs_le.mp (Real.norm_eq_abs (f w) ▸ hwC)
  have a2 := abs_le.mp (Real.norm_eq_abs (f z) ▸ hzC)
  linarith [a1.1, a1.2, a2.1, a2.2]

end PolyakAux

open Filter Topology ShorNonsmooth.Fejer in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (c : ℝ) (hM : (levelSet f c).Nonempty)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : ∀ k, x (k + 1) = polyakStep f g c γ (x k)) :
    (∃ kstar : ℕ, x kstar ∈ levelSet f c) ∨
      ∃ xbar ∈ levelSet f c, Tendsto x atTop (𝓝 xbar) := by
  by_cases hstop : ∃ k, x k ∈ levelSet f c
  · exact Or.inl hstop
  right
  push Not at hstop
  have hgt : ∀ k, c < f (x k) := fun k => by
    have := hstop k
    simp only [levelSet, Set.mem_ofPred_eq, not_le] at this
    exact this
  obtain ⟨y0, hy0⟩ := hM
  have hfc : Continuous f := hf.locallyLipschitz.continuous
  -- g (x k) ≠ 0
  have hgne : ∀ k, g (x k) ≠ 0 := by
    intro k h0
    have h1 := hg (x k) y0
    rw [h0, inner_zero_left] at h1
    have : f y0 ≤ c := hy0
    linarith [hgt k]
  set e : ℕ → ℝ := fun k => (f (x k) - c) ^ 2 / ‖g (x k)‖ ^ 2 with he
  have he0 : ∀ k, 0 ≤ e k := fun k => by positivity
  -- Fejer inequality
  have hfej : ∀ y ∈ levelSet f c, ∀ k,
      ‖x (k + 1) - y‖ ^ 2 + γ * (2 - γ) * e k ≤ ‖x k - y‖ ^ 2 := by
    intro y hy k
    have hstep : x (k + 1) = x k - (γ * (f (x k) - c) / ‖g (x k)‖ ^ 2) • g (x k) := by
      rw [hx k, polyakStep, if_neg]
      push Not
      exact ⟨hgt k, hgne k⟩
    have hsub : x (k + 1) - y = (x k - y) - (γ * (f (x k) - c) / ‖g (x k)‖ ^ 2) • g (x k) := by
      rw [hstep]; abel
    rw [hsub]
    apply PolyakAux.step_sq _ _ _ _ (by linarith [hgt k]) hγ0 (hgne k)
    have h1 := hg (x k) y
    have hy' : f y ≤ c := hy
    have : inner ℝ (g (x k)) (y - x k) = - inner ℝ (g (x k)) (x k - y) := by
      rw [← inner_neg_right, neg_sub]
    rw [this] at h1
    linarith
  have hκ : 0 < γ * (2 - γ) := by nlinarith
  have hanti : ∀ y ∈ levelSet f c, ∀ k, ‖x (k + 1) - y‖ ≤ ‖x k - y‖ := by
    intro y hy k
    have h := hfej y hy k
    have : ‖x (k + 1) - y‖ ^ 2 ≤ ‖x k - y‖ ^ 2 := by nlinarith [he0 k]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  have hantiM : ∀ y ∈ levelSet f c, Antitone (fun k => ‖x k - y‖) := fun y hy =>
    antitone_nat_of_succ_le (hanti y hy)
  set R := ‖x 0 - y0‖ with hR
  have hball : ∀ k, x k ∈ Metric.closedBall y0 R := by
    intro k
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hantiM y0 hy0 (Nat.zero_le k)
  -- summability of e
  have hpartial : ∀ N, ‖x N - y0‖ ^ 2 + γ * (2 - γ) * ∑ k ∈ Finset.range N, e k ≤ R ^ 2 := by
    intro N
    induction N with
    | zero => simp [hR]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hfej y0 hy0 N
      nlinarith
  have hsum : Summable e := by
    apply summable_of_sum_range_le he0 (c := R ^ 2 / (γ * (2 - γ)))
    intro N
    rw [le_div_iff₀ hκ]
    have := hpartial N
    nlinarith [sq_nonneg ‖x N - y0‖]
  have he_lim : Tendsto e atTop (𝓝 0) := hsum.tendsto_atTop_zero
  -- bounded subgradients
  obtain ⟨C, hC⟩ := (isCompact_closedBall y0 (R + 1)).exists_bound_of_continuousOn
    hfc.continuousOn
  have hgb : ∀ k, ‖g (x k)‖ ≤ 2 * C := fun k =>
    PolyakAux.subgrad_bound f y0 (x k) (g (x k)) R C hC (hball k) (hg (x k))
  -- f (x k) → c
  have hsq : Tendsto (fun k => (f (x k) - c) ^ 2) atTop (𝓝 0) := by
    have hlim2 : Tendsto (fun k => e k * (2 * C) ^ 2) atTop (𝓝 0) := by
      simpa using he_lim.mul_const ((2 * C) ^ 2)
    apply squeeze_zero (fun k => sq_nonneg _) _ hlim2
    intro k
    have hgpos : 0 < ‖g (x k)‖ := norm_pos_iff.mpr (hgne k)
    have h1 : (f (x k) - c) ^ 2 = e k * ‖g (x k)‖ ^ 2 := by
      rw [he]; field_simp
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ (he0 k)
    exact pow_le_pow_left₀ (norm_nonneg _) (hgb k) 2
  have hfx : Tendsto (fun k => f (x k)) atTop (𝓝 c) := by
    have habs : Tendsto (fun k => |f (x k) - c|) atTop (𝓝 0) := by
      have := hsq.sqrt
      simp only [Real.sqrt_zero] at this
      refine this.congr (fun k => ?_)
      exact Real.sqrt_sq_eq_abs _
    have h2 : Tendsto (fun k => f (x k) - c) atTop (𝓝 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
    simpa using h2.add_const c
  -- cluster point
  obtain ⟨xbar, -, φ, hφ, hφlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hball
  have hfxbar : f xbar = c := by
    have h1 : Tendsto (fun k => f (x (φ k))) atTop (𝓝 (f xbar)) :=
      (hfc.tendsto xbar).comp hφlim
    have h2 : Tendsto (fun k => f (x (φ k))) atTop (𝓝 c) :=
      hfx.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hxbarM : xbar ∈ levelSet f c := by
    show f xbar ≤ c
    rw [hfxbar]
  refine ⟨xbar, hxbarM, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hφd : Tendsto (fun k => ‖x (φ k) - xbar‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero).mp hφlim
    exact this
  obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.mp hφd) ε hε
  refine ⟨φ m, fun k hk => ?_⟩
  have h1 := hm m le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hantiM xbar hxbarM hk) h1
