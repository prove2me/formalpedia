-- Prove2me | solution 1 for TalagrandThinning.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:46:19.58371+00:00
-- url     : https://prove2.me/submissions/d0ae0fcd-3654-4825-9bc8-4ad6f0dcf248

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

namespace TTL32

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

lemma expect_sum {N : ℕ} (s : ℝ) {ι : Type} (S : Finset ι) (g : ι → Cube N → ℝ) :
    expect s (fun x => ∑ I ∈ S, g I x) = ∑ I ∈ S, expect s (g I) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma expect_const_mul {N : ℕ} (s c : ℝ) (g : Cube N → ℝ) :
    expect s (fun x => c * g x) = c * expect s g := by
  unfold expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma kernelK_eq {N : ℕ} (t p : ℝ) (j x w : Cube N) :
    kernelK t p j x w = ∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
      beta t p ^ I.card * omega t I x * omega p I w := by
  unfold kernelK kernelH
  rw [Finset.prod_one_add]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [omega]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]

theorem part1 {N : ℕ} (t p : ℝ) (f : Cube N → ℝ) (j x : Cube N) :
    liftL t p j f x =
      ∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
        beta t p ^ I.card * TalagrandThinning.fourierCoeff p f I * omega t I x := by
  unfold liftL
  simp_rw [kernelK_eq, Finset.sum_mul]
  rw [expect_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [TalagrandThinning.fourierCoeff]
  have : (fun w => beta t p ^ I.card * omega t I x * omega p I w * f w) =
      fun w => (beta t p ^ I.card * omega t I x) * (f w * omega p I w) := by
    funext w; ring
  rw [this, expect_const_mul]; ring

theorem part2 {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (f : Cube N → ℝ) (j : Cube N) :
    expect t (fun x => liftL t p j f x ^ 2) =
      ∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
        beta t p ^ (2 * I.card) * TalagrandThinning.fourierCoeff p f I ^ 2 := by
  set S := (Finset.univ.filter (fun i => j i = true)).powerset
  set a : Finset (Fin N) → ℝ := fun I => beta t p ^ I.card * TalagrandThinning.fourierCoeff p f I
  have e : ∀ x, liftL t p j f x ^ 2 =
      ∑ I ∈ S, ∑ K ∈ S, (a I * a K) * (omega t I x * omega t K x) := by
    intro x
    rw [part1, pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun K _ => ?_
    simp only [a]; ring
  simp_rw [e]
  rw [expect_sum]
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [expect_sum]
  simp_rw [expect_const_mul, expect_omega_mul_omega ht0 ht1]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq S I]
  rw [if_pos hI]
  simp only [a]; ring

end TTL32

open TalagrandThinning in
theorem solution {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube N → ℝ) (j : Cube N) :
    (∀ x : Cube N, liftL t p j f x =
      ∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
        beta t p ^ I.card * fourierCoeff p f I * omega t I x) ∧
    expect t (fun x => liftL t p j f x ^ 2) =
      ∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
        beta t p ^ (2 * I.card) * fourierCoeff p f I ^ 2 :=
  ⟨fun x => TTL32.part1 t p f j x, TTL32.part2 t p ht0 ht1 f j⟩
