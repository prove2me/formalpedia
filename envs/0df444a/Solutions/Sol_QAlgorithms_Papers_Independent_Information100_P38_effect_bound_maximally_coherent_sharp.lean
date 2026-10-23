-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.effect_bound_maximally_coherent_sharp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:50:35.663358+00:00
-- url     : https://prove2.me/submissions/23413509-931a-4cf6-ada9-1cbfb2565c66

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

namespace X6P38Sharp

lemma cs {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    Complex.normSq (star a ⬝ᵥ b) ≤ (star a ⬝ᵥ a).re * (star b ⬝ᵥ b).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 b) (WithLp.toLp 2 a)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  have e : a ⬝ᵥ star b = star (star a ⬝ᵥ b) := by simp [dotProduct, mul_comm]
  simp only at h
  rw [e, norm_star] at h
  have ha : ‖(WithLp.toLp 2 a : EuclideanSpace ℂ ι)‖ ^ 2 = (star a ⬝ᵥ a).re := by
    rw [← @inner_self_eq_norm_sq ℂ, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  have hb : ‖(WithLp.toLp 2 b : EuclideanSpace ℂ ι)‖ ^ 2 = (star b ⬝ᵥ b).re := by
    rw [← @inner_self_eq_norm_sq ℂ, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  rw [Complex.normSq_eq_norm_sq, ← ha, ← hb, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [h]) 2

lemma quad_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    star v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, conj (v i) * M i j * v j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def,
    mul_assoc]


open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38 in
lemma elem_le {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsEffect A) (v : EuclideanSpace ℂ (Fin d))
    (hv : IsState v) :
    (∑ i, ∑ j, conj (v i) * (A - energyDephasing A) i j * v j).re ≤ 1 - 1 / (d : ℝ) := by
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set x : Fin d → ℝ := fun i => ‖v i‖ with hx
  set a : Fin d → ℝ := fun i => (A i i).re with ha
  have hdiag : ∀ i, A i i = (a i : ℂ) := by
    intro i
    have h := hA.1.diag_nonneg (i := i)
    rw [Complex.nonneg_iff] at h
    exact Complex.ext rfl (by simp [a, h.2])
  have ha0 : ∀ i, 0 ≤ a i := fun i => (Complex.nonneg_iff.mp (hA.1.diag_nonneg (i := i))).1
  set s : Fin d → ℝ := fun i => Real.sqrt (a i) with hs
  -- off-diagonal bound via the square root
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.1
  set S := CFC.sqrt A with hSdef
  open scoped MatrixOrder in
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hSS : A = S * S := (CFC.sqrt_mul_sqrt_self A h0).symm
  have hentry : ∀ i j, A i j = star (fun k => S k i) ⬝ᵥ (fun k => S k j) := by
    intro i j
    rw [hSS, Matrix.mul_apply]
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have := hS.isHermitian.apply i k
    simpa using this.symm
  have hoff : ∀ i j, ‖A i j‖ ≤ s i * s j := by
    intro i j
    have h := cs (fun k => S k i) (fun k => S k j)
    rw [← hentry, ← hentry, ← hentry] at h
    rw [← Real.sqrt_mul (ha0 i), ← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt h
  -- unit norm
  have hx2 : ∑ i, x i ^ 2 = 1 := by
    have := hv
    unfold IsState at this
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at this
    simpa [x] using this
  -- quadratic form of A is at most one
  have hQ1 : (∑ i, ∑ j, conj (v i) * A i j * v j).re ≤ 1 := by
    have h := hA.2.dotProduct_mulVec_nonneg (fun i => v i)
    rw [quad_eq] at h
    have h' := (Complex.nonneg_iff.mp h).1
    simp only [Matrix.sub_apply, Matrix.one_apply, mul_sub, sub_mul, Finset.sum_sub_distrib,
      Complex.sub_re] at h'
    have : (∑ i, ∑ j, conj (v i) * (if i = j then (1 : ℂ) else 0) * v j).re = 1 := by
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [← hx2, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    linarith
  -- quadratic form of A is at most (∑ x s)^2
  have hQ2 : (∑ i, ∑ j, conj (v i) * A i j * v j).re ≤ (∑ i, x i * s i) ^ 2 := by
    rw [Complex.re_sum, sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := hoff i j
    have hxi : 0 ≤ x i := norm_nonneg _
    have hxj : 0 ≤ x j := norm_nonneg _
    calc ‖v i‖ * ‖A i j‖ * ‖v j‖ ≤ x i * (s i * s j) * x j := by
          gcongr
      _ = x i * s i * (x j * s j) := by ring
  -- diagonal part
  set T := ∑ i, a i * x i ^ 2 with hT
  have hdiagQ : (∑ i, ∑ j, conj (v i) * (A - energyDephasing A) i j * v j).re =
      (∑ i, ∑ j, conj (v i) * A i j * v j).re - T := by
    simp only [energyDephasing, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub, sub_mul,
      Finset.sum_sub_distrib, Complex.sub_re, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdiag, mul_comm (conj (v i)), mul_assoc, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hdiagQ]
  -- Cauchy-Schwarz
  have hCS : (∑ i, x i * s i) ^ 2 ≤ d * T := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => x i * s i)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at this
    have e : ∑ i, (x i * s i) ^ 2 = T := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (ha0 i)]; ring
    rw [e] at this; linarith
  set S2 := (∑ i, x i * s i) ^ 2
  have hTd : S2 / d ≤ T := by rw [div_le_iff₀ (by linarith)]; linarith
  have hinv : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hD
  by_cases hS1 : S2 ≤ 1
  · have : S2 - S2 / d ≤ 1 - 1 / d := by
      have e : S2 - S2 / d = S2 * (1 - 1 / d) := by ring
      rw [e]
      nlinarith [sq_nonneg (∑ i, x i * s i)]
    linarith
  · push Not at hS1
    have : 1 / (d : ℝ) < S2 / d := by
      apply div_lt_div_of_pos_right hS1 (by linarith)
    linarith

lemma re_of_nonneg {z : ℂ} (h : 0 ≤ z) : z = (z.re : ℂ) :=
  Complex.ext rfl (by simp [(Complex.nonneg_iff.mp h).2.symm])

end X6P38Sharp

open X6P38Sharp in
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution {d : ℕ} (hd : 0 < d)
    (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v)
    (hc : ∀ i, Complex.normSq (v i) = 1 / (d : ℝ)) :
    IsEffect (pureDensity v) ∧ energyDephasing (pureDensity v) = ((1 / (d : ℝ) : ℝ) : ℂ) • 1 ∧
    largestEnergyEigenvalue (pureDensity v - energyDephasing (pureDensity v)) = 1 - 1 / (d : ℝ) := by
  have hD : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : ∑ i, Complex.normSq (v i) = 1 := by
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hn' : star (fun i => v i) ⬝ᵥ (fun i => v i) = 1 := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    have : ∀ i, conj (v i) * v i = ((Complex.normSq (v i) : ℝ) : ℂ) := fun i => by
      rw [Complex.normSq_eq_conj_mul_self]
    simp only [this]
    exact_mod_cast hn
  have hPv : ∀ w : Fin d → ℂ, pureDensity v *ᵥ w = (star (fun i => v i) ⬝ᵥ w) • (fun i => v i) := by
    intro w; ext a
    simp only [pureDensity, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul, Pi.star_apply, RCLike.star_def, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hherm : (pureDensity v).IsHermitian := by
    ext i j; simp [pureDensity, mul_comm]
  have hz : ∀ w : Fin d → ℂ, star w ⬝ᵥ (pureDensity v *ᵥ w) =
      ((Complex.normSq (star w ⬝ᵥ (fun i => v i)) : ℝ) : ℂ) := by
    intro w
    rw [hPv, dotProduct_smul, smul_eq_mul, Complex.normSq_eq_conj_mul_self]
    congr 1
    simp [dotProduct, map_sum, mul_comm]
  have hE : IsEffect (pureDensity v) := by
    refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun w => ?_,
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_one.sub hherm) fun w => ?_⟩
    · rw [hz]; exact_mod_cast Complex.normSq_nonneg _
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hz,
        re_of_nonneg (dotProduct_star_self_nonneg w)]
      have h := cs w (fun i => v i)
      rw [hn', Complex.one_re, mul_one] at h
      exact_mod_cast sub_nonneg.mpr h
  have hdeph : energyDephasing (pureDensity v) = ((1 / (d : ℝ) : ℝ) : ℂ) • 1 := by
    ext i j
    simp only [energyDephasing, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · subst h
      simp only [pureDensity, Matrix.of_apply]
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, hc]
    · rfl
  refine ⟨hE, hdeph, ?_⟩
  have hbdd : BddAbove {r | ∃ w : EuclideanSpace ℂ (Fin d), IsState w ∧
      r = (∑ i, ∑ j, conj (w i) * (pureDensity v - energyDephasing (pureDensity v)) i j * w j).re} := by
    refine ⟨1 - 1 / (d : ℝ), ?_⟩
    rintro r ⟨w, hw, rfl⟩
    exact elem_le hd _ hE w hw
  unfold largestEnergyEigenvalue
  apply le_antisymm
  · refine csSup_le ⟨_, ⟨v, hv, rfl⟩⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    exact elem_le hd _ hE w hw
  · apply le_csSup hbdd
    refine ⟨v, hv, ?_⟩
    rw [hdeph]
    have : (∑ i, ∑ j, conj (v i) * (pureDensity v - ((1 / (d : ℝ) : ℝ) : ℂ) • 1) i j * v j) =
        star (fun i => v i) ⬝ᵥ ((pureDensity v - ((1 / (d : ℝ) : ℝ) : ℂ) • 1) *ᵥ (fun i => v i)) :=
      (quad_eq _ _).symm
    rw [this, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, hz, hn', smul_eq_mul, mul_one]
    simp
