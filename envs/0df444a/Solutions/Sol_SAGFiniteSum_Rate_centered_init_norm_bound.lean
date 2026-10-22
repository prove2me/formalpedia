-- Prove2me | solution 1 for SAGFiniteSum.Rate.centered_init_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:46:32.648171+00:00
-- url     : https://prove2.me/submissions/72a6016e-83e0-4fc5-ab5f-d6344d35c5b3

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
set_option autoImplicit false
open scoped InnerProductSpace

namespace ZZC4

variable {p : ℕ}

lemma line_deriv (φ : EuclideanSpace ℝ (Fin p) → ℝ) (G : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hG : ∀ x, HasGradientAt φ (G x) x) (x d : EuclideanSpace ℝ (Fin p)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + s • d)) (⟪G (x + t • d), d⟫_ℝ) t := by
  have h1 := (hG (x + t • d)).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have := h1.comp_hasDerivAt t h2
  rw [← InnerProductSpace.toDual_apply_apply]
  exact this

lemma descent (φ : EuclideanSpace ℝ (Fin p) → ℝ) (G : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hG : ∀ x, HasGradientAt φ (G x) x) (L : ℝ) (hL : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin p)) :
    φ y ≤ φ x + ⟪G x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  set ψ : ℝ → ℝ := fun t => φ (x + t • d) - t * ⟪G x, d⟫_ℝ - L / 2 * t ^ 2 * ‖d‖ ^ 2 with hψ
  have hψd : ∀ t : ℝ, HasDerivAt ψ (⟪G (x + t • d), d⟫_ℝ - ⟪G x, d⟫_ℝ - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := line_deriv φ G hG x d t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, d⟫_ℝ) (⟪G x, d⟫_ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (⟪G x, d⟫_ℝ)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
      exact this.congr_deriv (by first | ring | (norm_num; ring) | norm_num)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · intro t _
      exact (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hlip := hL (x + t • d) x
      have hnorm : ‖x + t • d - x‖ = t * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [hnorm] at hlip
      have hcs := real_inner_le_norm (G (x + t • d) - G x) d
      have e1 : ⟪G (x + t • d), d⟫_ℝ - ⟪G x, d⟫_ℝ = ⟪G (x + t • d) - G x, d⟫_ℝ := by rw [inner_sub_left]
      rw [e1]
      have : ‖G (x + t • d) - G x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at h01
  have : x + d = y := by simp [hd]
  rw [this] at h01
  nlinarith

lemma gradineq (φ : EuclideanSpace ℝ (Fin p) → ℝ) (G : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hG : ∀ x, HasGradientAt φ (G x) x) (hc : ConvexOn ℝ Set.univ φ)
    (x y : EuclideanSpace ℝ (Fin p)) :
    φ x + ⟪G x, y - x⟫_ℝ ≤ φ y := by
  set d := y - x with hd
  let g : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin p) :=
    { toFun := fun t => x + t • d
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight d
      map_vadd' := by intro p v; simp [add_smul]; abel }
  have hgc : ConvexOn ℝ (g ⁻¹' Set.univ) (φ ∘ g) := hc.comp_affineMap g
  have hc' : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t : ℝ => φ (x + t • d)) :=
    hgc.subset (Set.subset_univ _) (convex_Icc 0 1)
  have h0 : HasDerivAt (fun s : ℝ => φ (x + s • d)) (⟪G x, d⟫_ℝ) 0 := by
    have := line_deriv φ G hG x d 0
    simpa using this
  have := hc'.le_slope_of_hasDerivAt (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one h0
  rw [slope_def_field] at this
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at this
  have e : x + d = y := by simp [hd]
  rw [e] at this
  linarith

lemma cocoercive (f : EuclideanSpace ℝ (Fin p) → ℝ) (f' : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hG : ∀ x, HasGradientAt f (f' x) x) (hc : ConvexOn ℝ Set.univ f) (L : ℝ) (hL0 : 0 < L)
    (hL : ∀ x y, ‖f' x - f' y‖ ≤ L * ‖x - y‖) (x y : EuclideanSpace ℝ (Fin p)) :
    ‖f' x - f' y‖ ^ 2 ≤ 2 * L * (f x - f y - ⟪f' y, x - y⟫_ℝ) := by
  set φ : EuclideanSpace ℝ (Fin p) → ℝ := fun z => f z - ⟪f' y, z⟫_ℝ with hφ
  set G : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) := fun z => f' z - f' y with hGdef
  have hGφ : ∀ z, HasGradientAt φ (G z) z := by
    intro z
    have h2 : HasGradientAt (fun z => ⟪f' y, z⟫_ℝ) (f' y) z := by
      have : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin p) => ⟪f' y, z⟫_ℝ)
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p)) (f' y)) z :=
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p)) (f' y)).hasFDerivAt
      exact this
    have h3 := (hG z).hasFDerivAt.sub h2.hasFDerivAt
    rw [hasGradientAt_iff_hasFDerivAt]
    have e : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p)) (G z) =
        InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p)) (f' z) -
          InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p)) (f' y) := map_sub _ _ _
    rw [e]
    exact h3
  have hLG : ∀ a b, ‖G a - G b‖ ≤ L * ‖a - b‖ := by
    intro a b
    have : G a - G b = f' a - f' b := by simp [hGdef]
    rw [this]; exact hL a b
  have hmin : ∀ z, φ y ≤ φ z := by
    intro z
    have := gradineq f f' hG hc y z
    simp only [hφ]
    rw [inner_sub_right] at this
    linarith
  have hd := descent φ G hGφ L hLG x (x - (1 / L) • G x)
  have hmx := hmin (x - (1 / L) • G x)
  have e1 : x - (1 / L) • G x - x = -((1 / L) • G x) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_neg, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs] at hd
  have hGx : G x = f' x - f' y := rfl
  have e2 : φ x - φ y = f x - f y - ⟪f' y, x - y⟫_ℝ := by
    simp only [hφ, inner_sub_right]; ring
  have e3 : L / 2 * (1 / L) ^ 2 * ‖G x‖ ^ 2 = 1 / (2 * L) * ‖G x‖ ^ 2 := by field_simp
  have e4 : 1 / L * ‖G x‖ ^ 2 = 2 * (1 / (2 * L)) * ‖G x‖ ^ 2 := by field_simp
  rw [← hGx]
  have h5 : 0 ≤ ‖G x‖ ^ 2 := sq_nonneg _
  have h6 : ‖G x‖ ^ 2 / (2 * L) ≤ φ x - φ y := by
    have : L / 2 * ((1 / L) ^ 2 * ‖G x‖ ^ 2) = ‖G x‖ ^ 2 / (2 * L) / 1 := by field_simp
    have e5 : 1 / L * ‖G x‖ ^ 2 = 2 * (‖G x‖ ^ 2 / (2 * L)) := by field_simp
    rw [e5] at hd
    nlinarith
  rw [e2] at h6
  rw [div_le_iff₀ (by positivity)] at h6
  nlinarith

end ZZC4

theorem solution {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGFiniteSum.Rate.SAGAssumptions f f' L xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) :
    ∑ i, ‖SAGFiniteSum.Rate.centeredTable f' x0 i - f' i xstar‖ ^ 2
      ≤ 8 * (n : ℝ) * L * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar) := by
  have hn : 0 < n := hA.n_pos
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hL := hA.L_pos
  -- gradient of the average vanishes at the minimizer
  have hS : ∑ i, f' i xstar = 0 := by
    set d := ∑ i, f' i xstar with hd
    have hder : HasDerivAt (fun s : ℝ => SAGA.Convex.fAvg f (xstar + s • d))
        ((1 / (n : ℝ)) * ∑ i, ⟪f' i (xstar + (0:ℝ) • d), d⟫_ℝ) 0 := by
      unfold SAGA.Convex.fAvg
      have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ZZC4.line_deriv (f i) (f' i) (hA.hasGradient i) xstar d 0)
      exact (this.const_mul (1 / (n : ℝ)))
    have hmin : IsLocalMin (fun s : ℝ => SAGA.Convex.fAvg f (xstar + s • d)) 0 := by
      apply Filter.Eventually.of_forall
      intro s
      simpa using hA.minimizer (xstar + s • d)
    have h0 := hmin.hasDerivAt_eq_zero hder
    simp only [zero_smul, add_zero] at h0
    have : ∑ i, ⟪f' i xstar, d⟫_ℝ = ⟪d, d⟫_ℝ := by rw [← sum_inner]
    rw [this, real_inner_self_eq_norm_sq] at h0
    have h1 : ‖d‖ ^ 2 = 0 := by
      have := mul_eq_zero.mp h0
      rcases this with h | h
      · exact absurd h (by positivity)
      · exact h
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
  set a : Fin n → EuclideanSpace ℝ (Fin p) := fun i => f' i x0 - f' i xstar with ha
  set m : EuclideanSpace ℝ (Fin p) := (1 / (n : ℝ)) • ∑ i, a i with hm
  have hcen : ∀ i, SAGFiniteSum.Rate.centeredTable f' x0 i - f' i xstar = a i - m := by
    intro i
    have : SAGA.Convex.gradAvg f' x0 = m := by
      unfold SAGA.Convex.gradAvg
      rw [hm]
      congr 1
      simp only [ha, Finset.sum_sub_distrib, hS, sub_zero]
    simp only [SAGFiniteSum.Rate.centeredTable, this, ha]
    abel
  simp only [hcen]
  -- variance ≤ second moment
  have hvar : ∑ i, ‖a i - m‖ ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 := by
    have h1 : ∀ i, ‖a i - m‖ ^ 2 = ‖a i‖ ^ 2 - 2 * ⟪a i, m⟫_ℝ + ‖m‖ ^ 2 := fun i => norm_sub_sq_real _ _
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← sum_inner]
    have : ∑ i, a i = (n : ℝ) • m := by
      rw [hm, smul_smul, mul_one_div_cancel hnR.ne', one_smul]
    rw [this, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖m‖]
  -- cocoercivity
  have hcoc : ∀ i, ‖a i‖ ^ 2 ≤ 2 * L * (f i x0 - f i xstar - ⟪f' i xstar, x0 - xstar⟫_ℝ) := fun i =>
    ZZC4.cocoercive (f i) (f' i) (hA.hasGradient i) (hA.convex i) L hL (hA.lipschitz i) x0 xstar
  have hsum : ∑ i, ‖a i‖ ^ 2 ≤ 2 * L * ((n : ℝ) * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar)) := by
    calc ∑ i, ‖a i‖ ^ 2 ≤ ∑ i, 2 * L * (f i x0 - f i xstar - ⟪f' i xstar, x0 - xstar⟫_ℝ) :=
          Finset.sum_le_sum (fun i _ => hcoc i)
      _ = 2 * L * ((∑ i, f i x0) - (∑ i, f i xstar) - ⟪∑ i, f' i xstar, x0 - xstar⟫_ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_inner]
      _ = 2 * L * ((n : ℝ) * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar)) := by
          rw [hS, inner_zero_left]
          unfold SAGA.Convex.fAvg
          field_simp
          ring
  have hnn : 0 ≤ SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar := by
    have := hA.minimizer x0
    linarith
  nlinarith [mul_nonneg hnR.le hnn, mul_nonneg hL.le (mul_nonneg hnR.le hnn)]
