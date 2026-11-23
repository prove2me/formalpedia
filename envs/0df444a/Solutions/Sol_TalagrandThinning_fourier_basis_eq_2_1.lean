-- Prove2me | solution 1 for TalagrandThinning.fourier_basis_eq_2_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:37:08.0821+00:00
-- url     : https://prove2.me/submissions/b9ddfd9b-e823-4bfb-868d-4151fe7d01db

import Mathlib
import Definitions.Def_TalagrandThinning_fourierCoeff

set_option autoImplicit false

namespace TTFourier

open TalagrandThinning

/-- One-coordinate weight: `s` at `true`, `1 - s` at `false`. -/
noncomputable def w1 (s : ℝ) (b : Bool) : ℝ := if b then s else 1 - s

lemma w1_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (b : Bool) : 0 < w1 s b := by
  cases b <;> simp [w1] <;> linarith

lemma weight_eq_prod_w1 {N : ℕ} (s : ℝ) (x : Cube N) : weight s x = ∏ i, w1 s (x i) := rfl

lemma weight_pos {N : ℕ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : Cube N) : 0 < weight s x :=
  Finset.prod_pos fun i _ => w1_pos hs0 hs1 (x i)

/-- **Product structure** of `expect`: the expectation of a coordinatewise product is the product
of one-coordinate expectations. -/
theorem expect_prod {N : ℕ} (s : ℝ) (g : Fin N → Bool → ℝ) :
    expect s (fun x : Cube N => ∏ i, g i (x i)) =
      ∏ i, (s * g i true + (1 - s) * g i false) := by
  have h : ∀ i : Fin N, s * g i true + (1 - s) * g i false =
      ∑ b ∈ (Finset.univ : Finset Bool), w1 s b * g i b := by
    intro i; simp [w1]
  simp_rw [h]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  unfold expect
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [weight_eq_prod_w1, ← Finset.prod_mul_distrib]

lemma sqrt_sq_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.sqrt (s * (1 - s)) ^ 2 = s * (1 - s) :=
  Real.sq_sqrt (by nlinarith)

lemma sqrt_ne {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : Real.sqrt (s * (1 - s)) ≠ 0 :=
  (Real.sqrt_pos.2 (by nlinarith)).ne'

lemma phi_true (s : ℝ) : phi s true = (1 - s) / Real.sqrt (s * (1 - s)) := by simp [phi]
lemma phi_false (s : ℝ) : phi s false = (- s) / Real.sqrt (s * (1 - s)) := by simp [phi]

lemma phi_mean {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    s * phi s true + (1 - s) * phi s false = 0 := by
  have := sqrt_ne hs0 hs1
  rw [phi_true, phi_false]
  field_simp
  ring

lemma phi_sq_mean {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    s * phi s true ^ 2 + (1 - s) * phi s false ^ 2 = 1 := by
  have h1 := sqrt_ne hs0 hs1
  have h2 := sqrt_sq_eq hs0 hs1
  rw [phi_true, phi_false]; simp only [div_pow, h2]
  have : s * (1 - s) ≠ 0 := by nlinarith
  have : 1 - s ≠ 0 := by linarith
  field_simp
  ring

lemma omega_eq_prod_univ {N : ℕ} (s : ℝ) (I : Finset (Fin N)) (x : Cube N) :
    omega s I x = ∏ i, (if i ∈ I then phi s (x i) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]; rfl

/-- Orthonormality of the `ω_I`. -/
theorem expect_omega_mul_omega {N : ℕ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (I K : Finset (Fin N)) :
    expect s (fun x : Cube N => omega s I x * omega s K x) = if I = K then 1 else 0 := by
  have hm := phi_mean hs0 hs1
  have hq := phi_sq_mean hs0 hs1
  have e : (fun x : Cube N => omega s I x * omega s K x) = fun x => ∏ i,
      (fun i b => (if i ∈ I then phi s b else 1) * (if i ∈ K then phi s b else 1)) i (x i) := by
    funext x
    rw [omega_eq_prod_univ, omega_eq_prod_univ, ← Finset.prod_mul_distrib]
  rw [e, expect_prod s (fun i b => (if i ∈ I then phi s b else 1) * (if i ∈ K then phi s b else 1))]
  have h1 : ∀ i : Fin N,
      (s * ((if i ∈ I then phi s true else 1) * (if i ∈ K then phi s true else 1)) +
        (1 - s) * ((if i ∈ I then phi s false else 1) * (if i ∈ K then phi s false else 1))) =
      if (i ∈ I ↔ i ∈ K) then 1 else 0 := by
    intro i
    by_cases hI : i ∈ I <;> by_cases hK : i ∈ K <;> simp [hI, hK]
    · linear_combination hq
    · linear_combination hm
    · linear_combination hm
  simp only [h1]
  rw [Finset.prod_boole]
  congr 1
  apply propext
  simp [Finset.ext_iff]

lemma one_add_phi_mul_phi {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (a b : Bool) :
    1 + phi s a * phi s b = if a = b then (w1 s a)⁻¹ else 0 := by
  have h1 := sqrt_ne hs0 hs1
  have h2 := sqrt_sq_eq hs0 hs1
  have hs' : (1 - s) ≠ 0 := by linarith
  have hs'' : s ≠ 0 := hs0.ne'
  have key : ∀ u v : ℝ, u / Real.sqrt (s * (1 - s)) * (v / Real.sqrt (s * (1 - s))) =
      u * v / (s * (1 - s)) := by
    intro u v; rw [div_mul_div_comm, ← pow_two, h2]
  cases a <;> cases b <;> simp only [phi_true, phi_false, key, w1] <;> simp <;> field_simp <;> ring

/-- **Reproducing identity**: `∑_I ω_I(x) ω_I(y) = [x = y] / µ_s({x})`. -/
theorem sum_omega_mul_omega {N : ℕ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x y : Cube N) :
    ∑ I : Finset (Fin N), omega s I x * omega s I y = if x = y then (weight s x)⁻¹ else 0 := by
  have e : ∀ I : Finset (Fin N), omega s I x * omega s I y = ∏ i ∈ I, phi s (x i) * phi s (y i) := by
    intro I; simp only [omega]; rw [Finset.prod_mul_distrib]
  simp_rw [e]
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]
  simp_rw [one_add_phi_mul_phi hs0 hs1]
  split_ifs with hxy
  · subst hxy
    simp [weight_eq_prod_w1, Finset.prod_inv_distrib]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h; exact hxy (funext fun i => by by_contra hi; exact h ⟨i, hi⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Same identity, multiplied through by the weight. -/
theorem weight_mul_sum_omega_mul_omega {N : ℕ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (x y : Cube N) :
    weight s x * ∑ I : Finset (Fin N), omega s I x * omega s I y = if x = y then 1 else 0 := by
  rw [sum_omega_mul_omega hs0 hs1]
  split_ifs
  · exact mul_inv_cancel₀ (weight_pos hs0 hs1 x).ne'
  · simp

theorem fourier_expansion {N : ℕ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (f : Cube N → ℝ) (x : Cube N) :
    f x = ∑ I : Finset (Fin N), fourierCoeff s f I * omega s I x := by
  simp only [TalagrandThinning.fourierCoeff, expect, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y : Cube N, ∑ I : Finset (Fin N), weight s y * (f y * omega s I y) * omega s I x =
      f y * (weight s y * ∑ I : Finset (Fin N), omega s I y * omega s I x) := by
    intro y; rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => by ring
  simp_rw [this, weight_mul_sum_omega_mul_omega hs0 hs1]
  simp

theorem parseval {N : ℕ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (f : Cube N → ℝ) :
    expect s (fun x => f x ^ 2) = ∑ I : Finset (Fin N), fourierCoeff s f I ^ 2 := by
  have e : ∀ x : Cube N, f x ^ 2 = f x * ∑ I : Finset (Fin N), fourierCoeff s f I * omega s I x := by
    intro x; rw [← fourier_expansion hs0 hs1 f x]; ring
  simp_rw [e]
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [pow_two]
  conv_rhs => rw [TalagrandThinning.fourierCoeff, expect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [TalagrandThinning.fourierCoeff, expect]; ring

end TTFourier

open TalagrandThinning in
theorem solution {N : ℕ} (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (s * phi s true + (1 - s) * phi s false = 0) ∧
    (s * phi s true ^ 2 + (1 - s) * phi s false ^ 2 = 1) ∧
    (∀ I K : Finset (Fin N),
      expect s (fun x : Cube N => omega s I x * omega s K x) = if I = K then 1 else 0) ∧
    (∀ (f : Cube N → ℝ) (x : Cube N),
      f x = ∑ I : Finset (Fin N), fourierCoeff s f I * omega s I x) ∧
    (∀ f : Cube N → ℝ,
      expect s (fun x => f x ^ 2) = ∑ I : Finset (Fin N), fourierCoeff s f I ^ 2) :=
  ⟨TTFourier.phi_mean hs0 hs1, TTFourier.phi_sq_mean hs0 hs1,
    TTFourier.expect_omega_mul_omega hs0 hs1, TTFourier.fourier_expansion hs0 hs1,
    TTFourier.parseval hs0 hs1⟩
