-- Prove2me | solution 1 for SGDKaczmarz.SGD.eq_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:27:25.64106+00:00
-- url     : https://prove2.me/submissions/dee7c84b-5603-4519-adbb-db5b4f9bb5fd

import Mathlib

open scoped NNReal InnerProductSpace

section SGDAux
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem sgdaux_line_hasDerivAt (f : H → ℝ) (hf : Differentiable ℝ f) (x v : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪gradient f (x + t • v), v⟫_ℝ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have := (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline
  rw [show ⟪gradient f (x + t • v), v⟫_ℝ = fderiv ℝ f (x + t • v) v by
    rw [gradient, InnerProductSpace.toDual_symm_apply]]
  exact this

theorem sgdaux_descent (f : H → ℝ) (hf : Differentiable ℝ f) (L : ℝ≥0)
    (hL : LipschitzWith L (gradient f)) (x v : H) :
    f (x + v) ≤ f x + ⟪gradient f x, v⟫_ℝ + (L : ℝ) / 2 * ‖v‖ ^ 2 := by
  let φ : ℝ → ℝ := fun t => f (x + t • v) - f x - t * ⟪gradient f x, v⟫_ℝ -
    (L : ℝ) / 2 * t ^ 2 * ‖v‖ ^ 2
  have hφd : ∀ t, HasDerivAt φ (⟪gradient f (x + t • v), v⟫_ℝ - ⟪gradient f x, v⟫_ℝ -
      (L : ℝ) * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 := sgdaux_line_hasDerivAt f hf x v t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, v⟫_ℝ) ⟪gradient f x, v⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, v⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => (L : ℝ) / 2 * s ^ 2 * ‖v‖ ^ 2)
        ((L : ℝ) * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul ((L : ℝ) / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    exact ((h1.sub_const (f x)).sub h2).sub h3
  have hanti : AntitoneOn φ (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (fun t _ => (hφd t).continuousAt.continuousWithinAt)
    · exact fun t _ => (hφd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hφd t).deriv]
      have hlip : ‖gradient f (x + t • v) - gradient f x‖ ≤ (L : ℝ) * ‖t • v‖ := by
        have := hL.dist_le_mul (x + t • v) x
        simpa [dist_eq_norm] using this
      have hcs : ⟪gradient f (x + t • v) - gradient f x, v⟫_ℝ ≤
          ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := real_inner_le_norm _ _
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt ht)] at hlip
      have : ⟪gradient f (x + t • v), v⟫_ℝ - ⟪gradient f x, v⟫_ℝ =
          ⟪gradient f (x + t • v) - gradient f x, v⟫_ℝ := by rw [inner_sub_left]
      rw [this]
      have hv : 0 ≤ ‖v‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hlip hv]
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  simp only [φ, zero_smul, add_zero, sub_self, zero_mul, one_smul, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at this
  linarith

theorem sgdaux_first_order (f : H → ℝ) (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) (x z : H) :
    f x + ⟪gradient f x, z - x⟫_ℝ ≤ f z := by
  let g : ℝ → ℝ := fun s => f (x + s • (z - x))
  have hg : ConvexOn ℝ Set.univ g := by
    have := hconv.comp_affineMap (AffineMap.lineMap x z)
    rw [Set.preimage_univ] at this
    have hfun : g = f ∘ AffineMap.lineMap x z := by
      funext s
      simp only [g, Function.comp, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      congr 1; abel
    rw [hfun]; exact this
  have hd := sgdaux_line_hasDerivAt f hf x (z - x) 0
  simp only [zero_smul, add_zero] at hd
  have := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  simp only [g, one_smul, zero_smul, add_zero, sub_zero, div_one] at this
  have e : x + (z - x) = z := by abel
  rw [e] at this
  linarith

theorem sgdaux_cocoercive (f : H → ℝ) (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) (L : ℝ≥0) (hL0 : 0 < (L : ℝ))
    (hL : LipschitzWith L (gradient f)) (x y : H) :
    f x + ⟪gradient f x, y - x⟫_ℝ + 1 / (2 * (L : ℝ)) * ‖gradient f y - gradient f x‖ ^ 2
      ≤ f y := by
  set D := gradient f y - gradient f x with hD
  set z := y - (1 / (L : ℝ)) • D with hz
  have h1 := sgdaux_first_order f hf hconv x z
  have h2 := sgdaux_descent f hf L hL y (z - y)
  have e : y + (z - y) = z := by abel
  rw [e] at h2
  have hzy : z - y = -((1 / (L : ℝ)) • D) := by rw [hz]; abel
  have hzx : z - x = (y - x) - (1 / (L : ℝ)) • D := by rw [hz]; abel
  rw [hzx, inner_sub_right, inner_smul_right] at h1
  rw [hzy, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_of_nonneg (by positivity)] at h2
  have hDD : ⟪gradient f y, D⟫_ℝ - ⟪gradient f x, D⟫_ℝ = ‖D‖ ^ 2 := by
    rw [← inner_sub_left, ← hD, real_inner_self_eq_norm_sq]
  have hL' : (L : ℝ) ≠ 0 := hL0.ne'
  have : 1 / (L : ℝ) * ⟪gradient f y, D⟫_ℝ - 1 / (L : ℝ) * ⟪gradient f x, D⟫_ℝ =
      1 / (L : ℝ) * ‖D‖ ^ 2 := by rw [← mul_sub, hDD]
  have e2 : (L : ℝ) / 2 * (1 / (L : ℝ) * ‖D‖) ^ 2 = 1 / (2 * (L : ℝ)) * ‖D‖ ^ 2 := by
    field_simp
  have e3 : 1 / (L : ℝ) * ‖D‖ ^ 2 - 1 / (2 * (L : ℝ)) * ‖D‖ ^ 2 =
      1 / (2 * (L : ℝ)) * ‖D‖ ^ 2 := by field_simp; ring
  linarith

end SGDAux

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hf : Differentiable ℝ f) (L : ℝ≥0) (hL0 : 0 < L)
    (hL : LipschitzWith L (gradient f)) (xstar : H) (hmin : ∀ y, f xstar ≤ f y) (x : H) :
    1 / (2 * (L : ℝ)) * ‖gradient f x - gradient f xstar‖ ^ 2 ≤ f x - f xstar := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hzero : gradient f xstar = 0 := by
    have hlm : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
    have := hlm.hasFDerivAt_eq_zero (hf xstar).hasFDerivAt
    rw [gradient, this, map_zero]
  rw [hzero, sub_zero]
  set G := gradient f x
  have hd := sgdaux_descent f hf L hL x (-((1 / (L : ℝ)) • G))
  have hm := hmin (x + -((1 / (L : ℝ)) • G))
  rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg, norm_smul,
    Real.norm_of_nonneg (by positivity)] at hd
  have e : 1 / (L : ℝ) * ‖G‖ ^ 2 - (L : ℝ) / 2 * (1 / (L : ℝ) * ‖G‖) ^ 2 =
      1 / (2 * (L : ℝ)) * ‖G‖ ^ 2 := by field_simp; ring
  linarith
