-- Prove2me | solution 1 for SchauderBasis.not_exists_schauderBasis_L1_fourier
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:26:35.793273+00:00
-- url     : https://prove2.me/submissions/d9ce1bfa-e187-415c-8d02-b12816ec4462

import Mathlib

open Filter Topology MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace Sol_SchauderBasis_not_exists_schauderBasis_L1_fourier

lemma abs_sin_nat_mul_le (m : ℕ) (α : ℝ) : |Real.sin (m * α)| ≤ m * |Real.sin α| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : Real.sin (((m + 1 : ℕ) : ℝ) * α)
        = Real.sin (m * α) * Real.cos α + Real.cos (m * α) * Real.sin α := by
      rw [← Real.sin_add]; push_cast; ring_nf
    rw [h]
    calc |Real.sin (m * α) * Real.cos α + Real.cos (m * α) * Real.sin α|
        ≤ |Real.sin (m * α) * Real.cos α| + |Real.cos (m * α) * Real.sin α| := abs_add_le _ _
      _ ≤ |Real.sin (m * α)| + |Real.sin α| := by
          apply add_le_add
          · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
          · rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ m * |Real.sin α| + |Real.sin α| := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * |Real.sin α| := by push_cast; ring

lemma two_sin_mul_sum_sin (θ a : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range n, Real.sin ((a + k) * θ)
      = Real.cos ((a - 1 / 2) * θ) - Real.cos ((a + n - 1 / 2) * θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : Real.cos ((a + n - 1 / 2) * θ)
        = Real.cos ((a + n) * θ) * Real.cos (θ / 2) + Real.sin ((a + n) * θ) * Real.sin (θ / 2) := by
      rw [← Real.cos_sub]; ring_nf
    have h2 : Real.cos ((a + ((n + 1 : ℕ) : ℝ) - 1 / 2) * θ)
        = Real.cos ((a + n) * θ) * Real.cos (θ / 2) - Real.sin ((a + n) * θ) * Real.sin (θ / 2) := by
      rw [← Real.cos_add]; push_cast; ring_nf
    rw [h1, h2]; ring

lemma abs_sum_sin_le (θ a : ℝ) (n : ℕ) (hs : Real.sin (θ / 2) ≠ 0) :
    |∑ k ∈ Finset.range n, Real.sin ((a + k) * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have h := two_sin_mul_sum_sin θ a n
  have hpos : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hs
  rw [le_div_iff₀ hpos]
  have h2 : |2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range n, Real.sin ((a + k) * θ)| ≤ 2 := by
    rw [h]
    calc _ ≤ |Real.cos ((a - 1 / 2) * θ)| + |Real.cos ((a + n - 1 / 2) * θ)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      _ = 2 := by norm_num
  rw [abs_mul, abs_mul, abs_two] at h2
  linarith

lemma abel_bound (w x : ℕ → ℝ) (B : ℝ) (hw : Antitone w) (hw0 : ∀ k, 0 ≤ w k)
    (hS : ∀ j, |∑ k ∈ Finset.range j, x k| ≤ B) (n : ℕ) :
    |∑ k ∈ Finset.range n, w k * x k| ≤ B * w 0 := by
  have key : ∀ n : ℕ, |∑ k ∈ Finset.range n, w k * x k - w n * ∑ k ∈ Finset.range n, x k|
      ≤ B * (w 0 - w n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ∑ k ∈ Finset.range (n + 1), w k * x k - w (n + 1) * ∑ k ∈ Finset.range (n + 1), x k
          = (∑ k ∈ Finset.range n, w k * x k - w n * ∑ k ∈ Finset.range n, x k)
            + (w n - w (n + 1)) * ∑ k ∈ Finset.range (n + 1), x k := by
        simp only [Finset.sum_range_succ]; ring
      rw [e]
      have hd : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hw (Nat.le_succ n))
      have h3 : |(w n - w (n + 1)) * ∑ k ∈ Finset.range (n + 1), x k| ≤ (w n - w (n + 1)) * B := by
        rw [abs_mul, abs_of_nonneg hd]; exact mul_le_mul_of_nonneg_left (hS _) hd
      calc _ ≤ |∑ k ∈ Finset.range n, w k * x k - w n * ∑ k ∈ Finset.range n, x k|
            + |(w n - w (n + 1)) * ∑ k ∈ Finset.range (n + 1), x k| := abs_add_le _ _
        _ ≤ B * (w 0 - w n) + (w n - w (n + 1)) * B := add_le_add ih h3
        _ = B * (w 0 - w (n + 1)) := by ring
  have h1 := key n
  have h2 : |w n * ∑ k ∈ Finset.range n, x k| ≤ w n * B := by
    rw [abs_mul, abs_of_nonneg (hw0 n)]; exact mul_le_mul_of_nonneg_left (hS n) (hw0 n)
  have e : ∑ k ∈ Finset.range n, w k * x k
      = (∑ k ∈ Finset.range n, w k * x k - w n * ∑ k ∈ Finset.range n, x k)
        + w n * ∑ k ∈ Finset.range n, x k := by ring
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ B * (w 0 - w n) + w n * B := add_le_add h1 h2
    _ = B * w 0 := by ring

lemma abs_sum_sin_div_le (θ : ℝ) (N : ℕ) :
    |∑ k ∈ Finset.range N, Real.sin ((k + 1) * θ) / (k + 1)| ≤ 3 := by
  set s := |Real.sin (θ / 2)| with hs_def
  have hs0 : 0 ≤ s := abs_nonneg _
  have hterm : ∀ k : ℕ, |Real.sin ((k + 1) * θ)| ≤ 2 * (k + 1) * s := by
    intro k
    have h := abs_sin_nat_mul_le (2 * (k + 1)) (θ / 2)
    have e : ((2 * (k + 1) : ℕ) : ℝ) * (θ / 2) = (k + 1) * θ := by push_cast; ring
    rw [e] at h
    calc _ ≤ _ := h
      _ = 2 * (k + 1) * s := by push_cast; ring
  have hhead : ∀ M : ℕ, |∑ k ∈ Finset.range M, Real.sin ((k + 1) * θ) / (k + 1)| ≤ 2 * M * s := by
    intro M
    calc _ ≤ ∑ k ∈ Finset.range M, |Real.sin ((k + 1) * θ) / (k + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range M, 2 * s := by
          apply Finset.sum_le_sum; intro k _
          have hk : (0 : ℝ) < k + 1 := by positivity
          rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
          have := hterm k; nlinarith
      _ = 2 * M * s := by simp; ring
  rcases eq_or_ne (Real.sin (θ / 2)) 0 with h0 | h0
  · have hs : s = 0 := by simp [hs_def, h0]
    have := hhead N
    rw [hs, mul_zero] at this
    linarith
  · have hspos : 0 < s := abs_pos.mpr h0
    set M := ⌊1 / s⌋₊ with hM
    have hMs : (M : ℝ) * s ≤ 1 := by
      have h1 : (M : ℝ) ≤ 1 / s := Nat.floor_le (one_div_nonneg.mpr hs0)
      calc (M : ℝ) * s ≤ (1 / s) * s := by gcongr
        _ = 1 := by field_simp
    have hMs' : 1 < ((M : ℝ) + 1) * s := by
      have h1 : 1 / s < (M : ℝ) + 1 := Nat.lt_floor_add_one (1 / s)
      calc (1 : ℝ) = (1 / s) * s := by field_simp
        _ < ((M : ℝ) + 1) * s := by gcongr
    rcases le_or_gt N M with hNM | hNM
    · have h1 := hhead N
      have h2 : (N : ℝ) * s ≤ M * s := by gcongr
      linarith
    · obtain ⟨L, rfl⟩ : ∃ L, N = M + L := ⟨N - M, by omega⟩
      rw [Finset.sum_range_add]
      have htail : |∑ k ∈ Finset.range L,
          Real.sin ((((M + k : ℕ) : ℝ) + 1) * θ) / (((M + k : ℕ) : ℝ) + 1)| ≤ 1 := by
        have hab := abel_bound (fun k : ℕ => 1 / ((M : ℝ) + 1 + k))
          (fun k : ℕ => Real.sin (((M : ℝ) + 1 + k) * θ)) (1 / s) ?_ ?_ ?_ L
        · have e : ∑ k ∈ Finset.range L,
              Real.sin ((((M + k : ℕ) : ℝ) + 1) * θ) / (((M + k : ℕ) : ℝ) + 1)
              = ∑ k ∈ Finset.range L, (fun k : ℕ => 1 / ((M : ℝ) + 1 + k)) k *
                  (fun k : ℕ => Real.sin (((M : ℝ) + 1 + k) * θ)) k := by
            apply Finset.sum_congr rfl; intro k _
            simp only
            push_cast
            rw [show (M : ℝ) + k + 1 = M + 1 + k by ring]
            ring
          rw [e]
          calc _ ≤ _ := hab
            _ = 1 / (((M : ℝ) + 1) * s) := by rw [Nat.cast_zero, add_zero]; field_simp
            _ ≤ 1 := by
                rw [div_le_one (by positivity)]; linarith
        · intro i j hij
          simp only
          apply one_div_le_one_div_of_le (by positivity)
          have : (i : ℝ) ≤ j := by exact_mod_cast hij
          linarith
        · intro k; positivity
        · intro j
          exact abs_sum_sin_le θ ((M : ℝ) + 1) j h0
      calc _ ≤ |∑ k ∈ Finset.range M, Real.sin ((k + 1) * θ) / (k + 1)|
            + |∑ k ∈ Finset.range L,
              Real.sin ((((M + k : ℕ) : ℝ) + 1) * θ) / (((M + k : ℕ) : ℝ) + 1)| := abs_add_le _ _
        _ ≤ 2 * M * s + 1 := add_le_add (hhead M) htail
        _ ≤ 3 := by linarith


open Complex in
lemma fourier_sub_fourier_apply (T : ℝ) [Fact (0 < T)] (N k : ℕ) (hk : k ≤ N) (t : ℝ) :
    fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) (t : AddCircle T)
        - fourier (T := T) (((N - k : ℕ) : ℤ)) (t : AddCircle T)
      = Complex.exp (((N + 1 : ℝ) * (2 * Real.pi * t / T) : ℝ) * I)
        * (2 * I * ((Real.sin ((k + 1) * (2 * Real.pi * t / T)) : ℝ) : ℂ)) := by
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < T).ne'
  rw [fourier_coe_apply, fourier_coe_apply]
  set u : ℝ := (N + 1 : ℝ) * (2 * Real.pi * t / T)
  set v : ℝ := (k + 1) * (2 * Real.pi * t / T)
  have e1 : Complex.exp (2 * Real.pi * I * (((N + k + 2 : ℕ) : ℤ) : ℂ) * t / T)
      = Complex.exp (u * I) * Complex.exp (v * I) := by
    rw [← Complex.exp_add]; congr 1
    simp only [u, v]; push_cast; field_simp; ring
  have e2 : Complex.exp (2 * Real.pi * I * (((N - k : ℕ) : ℤ) : ℂ) * t / T)
      = Complex.exp (u * I) * Complex.exp (-(v * I)) := by
    rw [← Complex.exp_add]; congr 1
    simp only [u, v]
    rw [Int.natCast_sub hk]; push_cast; field_simp; ring
  rw [e1, e2, ← mul_sub]
  congr 1
  rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_sin]
  ring

lemma norm_fourier_test_le (T : ℝ) [Fact (0 < T)] (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1)) •
        (fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) - fourier (T := T) (((N - k : ℕ) : ℤ)))‖ ≤ 6 := by
  rw [ContinuousMap.norm_le _ (by norm_num)]
  intro x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  set θ : ℝ := 2 * Real.pi * t / T
  have h : (∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1)) •
        (fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) - fourier (T := T) (((N - k : ℕ) : ℤ))))
          (QuotientAddGroup.mk t)
      = Complex.exp (((N + 1 : ℝ) * θ : ℝ) * Complex.I) * (2 * Complex.I *
          ((∑ k ∈ Finset.range N, Real.sin ((k + 1) * θ) / (k + 1) : ℝ) : ℂ)) := by
    rw [ContinuousMap.sum_apply, Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := (Finset.mem_range.mp hk).le
    rw [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul]
    have := fourier_sub_fourier_apply T N k hkN t
    erw [this]
    simp only [θ]
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_I, Complex.norm_two, mul_one, Real.norm_eq_abs]
  have := abs_sum_sin_div_le θ N
  linarith


def zeta (n : ℕ) : ℤ := if Odd n then (((n + 1) / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)

lemma zeta_surjective : Function.Surjective zeta := by
  intro n
  refine ⟨if 0 < n then 2 * n.toNat - 1 else 2 * (-n).toNat, ?_⟩
  simp only [zeta, Nat.odd_iff]
  split_ifs <;> omega

lemma lt_iff_zeta (N j : ℕ) :
    j < N ↔ (-(((N : ℤ) - 1) / 2) ≤ zeta j ∧ zeta j ≤ (N : ℤ) / 2) := by
  simp only [zeta, Nat.odd_iff]
  split_ifs <;> omega

variable {T : ℝ} [hT : Fact (0 < T)]

lemma integrable_star_mul (φ : C(AddCircle T, ℂ)) (u : Lp ℂ 1 (haarAddCircle (T := T))) :
    Integrable (fun t => star (φ t) * (u : AddCircle T → ℂ) t) haarAddCircle :=
  (L1.integrable_coeFn u).bdd_mul (c := ‖φ‖) φ.continuous.star.aestronglyMeasurable
    (ae_of_all _ fun t => by rw [norm_star]; exact φ.norm_coe_le_norm t)

/-- Integration against the conjugate of a continuous function, as a linear functional on `L¹`. -/
noncomputable def pairL (φ : C(AddCircle T, ℂ)) : Lp ℂ 1 (haarAddCircle (T := T)) →ₗ[ℂ] ℂ where
  toFun u := ∫ t, star (φ t) * (u : AddCircle T → ℂ) t ∂haarAddCircle
  map_add' u v := by
    have h : (fun t => star (φ t) * (⇑(u + v) : AddCircle T → ℂ) t) =ᵐ[haarAddCircle]
        fun t => star (φ t) * (u : AddCircle T → ℂ) t + star (φ t) * (v : AddCircle T → ℂ) t := by
      filter_upwards [Lp.coeFn_add u v] with t ht
      rw [ht, Pi.add_apply, mul_add]
    rw [integral_congr_ae h, integral_add (integrable_star_mul φ u) (integrable_star_mul φ v)]
  map_smul' c u := by
    have h : (fun t => star (φ t) * (⇑(c • u) : AddCircle T → ℂ) t) =ᵐ[haarAddCircle]
        fun t => c * (star (φ t) * (u : AddCircle T → ℂ) t) := by
      filter_upwards [Lp.coeFn_smul c u] with t ht
      rw [ht, Pi.smul_apply, smul_eq_mul]; ring
    rw [RingHom.id_apply, smul_eq_mul, integral_congr_ae h, integral_const_mul]

lemma norm_pairL_le (φ : C(AddCircle T, ℂ)) (u : Lp ℂ 1 (haarAddCircle (T := T))) :
    ‖pairL φ u‖ ≤ ‖φ‖ * ‖u‖ := by
  show ‖∫ t, star (φ t) * (u : AddCircle T → ℂ) t ∂haarAddCircle‖ ≤ ‖φ‖ * ‖u‖
  rw [L1.norm_eq_integral_norm, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn u).norm.const_mul _)
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm t) (norm_nonneg _)

/-- The pairing `u ↦ ∫ conj(φ) u` as a continuous linear functional on `L¹`. -/
noncomputable def pair (φ : C(AddCircle T, ℂ)) : StrongDual ℂ (Lp ℂ 1 (haarAddCircle (T := T))) :=
  (pairL φ).mkContinuous ‖φ‖ (norm_pairL_le φ)

lemma pair_apply (φ : C(AddCircle T, ℂ)) (u : Lp ℂ 1 (haarAddCircle (T := T))) :
    pair φ u = ∫ t, star (φ t) * (u : AddCircle T → ℂ) t ∂haarAddCircle := rfl

lemma norm_pair_apply_le (φ : C(AddCircle T, ℂ)) (u : Lp ℂ 1 (haarAddCircle (T := T))) :
    ‖pair φ u‖ ≤ ‖φ‖ * ‖u‖ := norm_pairL_le φ u

lemma pair_add (φ ψ : C(AddCircle T, ℂ)) : pair (φ + ψ) = pair φ + pair ψ := by
  ext u
  simp only [ContinuousLinearMap.add_apply, pair_apply, ContinuousMap.add_apply, star_add, add_mul]
  exact integral_add (integrable_star_mul φ u) (integrable_star_mul ψ u)

lemma pair_sub (φ ψ : C(AddCircle T, ℂ)) : pair (φ - ψ) = pair φ - pair ψ := by
  ext u
  simp only [ContinuousLinearMap.sub_apply, pair_apply, ContinuousMap.sub_apply, star_sub, sub_mul]
  exact integral_sub (integrable_star_mul φ u) (integrable_star_mul ψ u)

lemma pair_neg (φ : C(AddCircle T, ℂ)) : pair (-φ) = -pair φ := by
  ext u
  simp only [ContinuousLinearMap.neg_apply, pair_apply, ContinuousMap.neg_apply, star_neg, neg_mul]
  exact integral_neg _

lemma pair_smul (c : ℂ) (φ : C(AddCircle T, ℂ)) : pair (c • φ) = star c • pair φ := by
  ext u
  simp only [ContinuousLinearMap.smul_apply, pair_apply, ContinuousMap.smul_apply, smul_eq_mul,
    star_mul', mul_assoc]
  exact integral_const_mul _ _

lemma pair_zero : pair (0 : C(AddCircle T, ℂ)) = 0 := by
  ext u
  simp [pair_apply]

lemma pair_sum {ι : Type*} (s : Finset ι) (f : ι → C(AddCircle T, ℂ)) :
    pair (∑ i ∈ s, f i) = ∑ i ∈ s, pair (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add, ih]

lemma pair_fourier_fourierLp (j k : ℤ) :
    pair (fourier (T := T) j) (fourierLp (T := T) 1 k) = (Pi.single k (1 : ℂ) : ℤ → ℂ) j := by
  rw [pair_apply]
  have h : (fun t => star (fourier (T := T) j t) * (fourierLp (T := T) 1 k : AddCircle T → ℂ) t)
      =ᵐ[haarAddCircle] fun t => fourier (T := T) (-j) t • fourier (T := T) k t := by
    filter_upwards [coeFn_fourierLp (T := T) 1 k] with t ht
    rw [ht, fourier_neg, smul_eq_mul]
    rfl
  rw [integral_congr_ae h]
  have := congrFun (fourierCoeff_fourier (T := T) k) j
  rw [fourierCoeff] at this
  exact this

lemma pair_sum_fourier_eq_zero (s : Finset ℕ) (c : ℕ → ℂ) (f : ℕ → ℤ) (k : ℤ)
    (h : ∀ j ∈ s, f j ≠ k) :
    pair (∑ j ∈ s, c j • fourier (T := T) (f j)) (fourierLp (T := T) 1 k) = 0 := by
  rw [pair_sum, ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [pair_smul, ContinuousLinearMap.smul_apply, pair_fourier_fourierLp, Pi.single_apply,
    if_neg (h j hj), smul_zero]

end Sol_SchauderBasis_not_exists_schauderBasis_L1_fourier

open Sol_SchauderBasis_not_exists_schauderBasis_L1_fourier in
theorem solution (T : ℝ) [Fact (0 < T)] :
    ¬ ∃ b : SchauderBasis ℂ (Lp ℂ 1 (haarAddCircle (T := T))),
      ∀ n : ℕ, b.basis n = fourierLp (T := T) 1 (if Odd n then (((n + 1) / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) := by
  rintro ⟨b, hb⟩
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hbound : ∀ N : ℕ, 0 < N → ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1)) ≤ 12 * C := by
    intro N hN
    set A : C(AddCircle T, ℂ) := ∑ k ∈ Finset.range N,
      (1 / ((k : ℂ) + 1)) • fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) with hA
    set B : C(AddCircle T, ℂ) := ∑ k ∈ Finset.range N,
      (1 / ((k : ℂ) + 1)) • fourier (T := T) (((N - k : ℕ) : ℤ)) with hB
    have hAB : A - B = ∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1)) •
        (fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) - fourier (T := T) (((N - k : ℕ) : ℤ))) := by
      rw [hA, hB, ← Finset.sum_sub_distrib]
      simp_rw [smul_sub]
    have hψ : ‖A - B‖ ≤ 6 := hAB ▸ norm_fourier_test_le T N
    -- transposing the partial sum operator
    have hkey : (pair (A - B)).comp (b.proj (2 * N + 1)) = pair (-B) := by
      apply ContinuousLinearMap.ext_on (s := Set.range (fourierLp (T := T) 1))
      · rw [Submodule.dense_iff_topologicalClosure_eq_top]
        exact span_fourierLp_closure_eq_top (by norm_num)
      · rintro _ ⟨k, rfl⟩
        obtain ⟨i, hi⟩ := zeta_surjective k
        have hbi : b.basis i = fourierLp (T := T) 1 k := by
          rw [hb i]
          show fourierLp (T := T) 1 (zeta i) = _
          rw [hi]
        have hiff := lt_iff_zeta (2 * N + 1) i
        rw [hi] at hiff
        push_cast at hiff
        rw [ContinuousLinearMap.comp_apply, ← hbi, b.proj_apply_basis_mem, hbi]
        split_ifs with h
        · have hk := hiff.mp h
          rw [pair_sub, pair_neg, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
            hA, pair_sum_fourier_eq_zero, zero_sub]
          intro j _
          omega
        · rw [map_zero, pair_neg, ContinuousLinearMap.neg_apply, hB, pair_sum_fourier_eq_zero,
            neg_zero]
          intro j hj
          have hjN := Finset.mem_range.mp hj
          omega
    -- the test function in `L¹`: the indicator of a neighbourhood of `0`
    set H : ℝ := ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1)) with hH
    have hHpos : 0 < H :=
      Finset.sum_pos (fun k _ => by positivity) (Finset.nonempty_range_iff.mpr hN.ne')
    have hB0 : ((-B) 0).re = -H := by
      rw [hB, ContinuousMap.neg_apply, ContinuousMap.sum_apply, hH]
      simp only [ContinuousMap.smul_apply, fourier_eval_zero, smul_eq_mul, mul_one]
      rw [Complex.neg_re, Complex.re_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      have : (1 / ((k : ℂ) + 1)) = ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
    set U : Set (AddCircle T) := {t | ((-B) t).re < -(H / 2)} with hU
    have hUo : IsOpen U := isOpen_lt (Complex.continuous_re.comp (-B).continuous) continuous_const
    have hUm : MeasurableSet U := hUo.measurableSet
    have h0U : (0 : AddCircle T) ∈ U := by
      show ((-B) 0).re < -(H / 2)
      rw [hB0]; linarith
    have hUpos : 0 < haarAddCircle (T := T) U := hUo.measure_pos _ ⟨0, h0U⟩
    have hUfin : haarAddCircle (T := T) U ≠ ∞ := measure_ne_top _ _
    have hUreal : 0 < (haarAddCircle (T := T)).real U := ENNReal.toReal_pos hUpos.ne' hUfin
    set u : Lp ℂ 1 (haarAddCircle (T := T)) := indicatorConstLp 1 hUm hUfin (1 : ℂ) with hu
    have hnu : ‖u‖ = (haarAddCircle (T := T)).real U := by
      rw [hu, norm_indicatorConstLp one_ne_zero one_ne_top]
      simp
    have hpu : pair (-B) u = ∫ t in U, star ((-B) t) ∂haarAddCircle := by
      rw [pair_apply, ← integral_indicator hUm]
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hUm) (hμs := hUfin) (c := (1 : ℂ))]
        with t ht
      rw [ht]
      by_cases htU : t ∈ U
      · simp [Set.indicator_of_mem htU]
      · simp [Set.indicator_of_notMem htU]
    have hint : Integrable (fun t => star ((-B) t)) (haarAddCircle (T := T)) :=
      (-B).continuous.star.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hre : (pair (-B) u).re ≤ (haarAddCircle (T := T)).real U * (-(H / 2)) := by
      rw [hpu, ← RCLike.re_to_complex, ← integral_re hint.integrableOn]
      calc ∫ t in U, RCLike.re (star ((-B) t)) ∂haarAddCircle
          ≤ ∫ t in U, (-(H / 2)) ∂haarAddCircle := by
            refine setIntegral_mono_on hint.integrableOn.re (integrableOn_const ?_) hUm ?_
            · exact hUfin
            · intro t ht
              rw [RCLike.star_def, RCLike.conj_re, RCLike.re_to_complex]
              exact ht.le
        _ = _ := by rw [setIntegral_const, smul_eq_mul]
    have hupper : ‖pair (-B) u‖ ≤ 6 * C * (haarAddCircle (T := T)).real U := by
      rw [← hkey, ContinuousLinearMap.comp_apply]
      calc ‖pair (A - B) (b.proj (2 * N + 1) u)‖ ≤ ‖A - B‖ * ‖b.proj (2 * N + 1) u‖ :=
            norm_pair_apply_le _ _
        _ ≤ 6 * (C * ‖u‖) := by
            apply mul_le_mul hψ _ (norm_nonneg _) (by norm_num)
            exact ((b.proj (2 * N + 1)).le_opNorm u).trans
              (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
        _ = 6 * C * (haarAddCircle (T := T)).real U := by rw [hnu]; ring
    have hlower : (haarAddCircle (T := T)).real U * (H / 2) ≤ ‖pair (-B) u‖ := by
      have := (neg_le_abs (pair (-B) u).re).trans (Complex.abs_re_le_norm _)
      nlinarith
    have : (haarAddCircle (T := T)).real U * (H / 2) ≤
        (haarAddCircle (T := T)).real U * (6 * C) := by linarith
    have := le_of_mul_le_mul_left this hUreal
    linarith
  obtain ⟨N, hN, hN0⟩ :=
    ((Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop (12 * C)).and
      (eventually_gt_atTop 0)).exists
  exact absurd (hbound N hN0) (not_le.mpr hN)
