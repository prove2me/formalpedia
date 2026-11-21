-- Prove2me | solution 1 for PSDPolyApprox.lemma_1_general
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:10:18.406088+00:00
-- url     : https://prove2.me/submissions/e9015425-b705-4416-8e1d-35a42b6ee795

import Mathlib
import Definitions.Def_PSDPolyApprox_noise
import Definitions.Def_PSDPolyApprox_prob

namespace PSDPolyApprox

namespace Aux_L1G

open Finset

/-! ### Kernel form of the noise operator -/

noncomputable def K {n : ℕ} (a : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, (1 + a * (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)))

noncomputable def T {n : ℕ} (a : ℝ) (h : Cube n → ℝ) (x : Cube n) : ℝ :=
  ((2:ℝ) ^ n)⁻¹ * ∑ y, h y * K a x y

lemma sum_units (F : ℤˣ → ℝ) : ∑ u, F u = F 1 + F (-1) := by
  apply Fintype.sum_eq_add 1 (-1) (by decide)
  intro x hx
  rcases Int.units_eq_one_or x with h | h
  · exact absurd h hx.1
  · exact absurd h hx.2

lemma sum_prod_cube {n : ℕ} (g : Fin n → ℤˣ → ℝ) :
    ∑ y : Cube n, ∏ i, g i (y i) = ∏ i, ∑ u, g i u := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma K_comm {n : ℕ} (a : ℝ) (x y : Cube n) : K a x y = K a y x := by
  unfold K
  exact Finset.prod_congr rfl (fun i _ => by ring)

lemma K_sum {n : ℕ} (a : ℝ) (x : Cube n) : ∑ y, K a x y = (2:ℝ) ^ n := by
  have h := sum_prod_cube (fun i (u : ℤˣ) => 1 + a * (((x i : ℤ) : ℝ) * ((u : ℤ) : ℝ)))
  have h2 : ∀ i : Fin n, ∑ u : ℤˣ, (1 + a * (((x i : ℤ) : ℝ) * ((u : ℤ) : ℝ))) = 2 := by
    intro i
    rw [sum_units]
    simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]
    ring
  calc ∑ y, K a x y
      = ∏ i, ∑ u : ℤˣ, (1 + a * (((x i : ℤ) : ℝ) * ((u : ℤ) : ℝ))) := h
    _ = ∏ _i : Fin n, (2:ℝ) := Finset.prod_congr rfl (fun i _ => h2 i)
    _ = (2:ℝ) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

noncomputable def g2 {n : ℕ} (a b : ℝ) (x z : Cube n) (i : Fin n) (u : ℤˣ) : ℝ :=
  (1 + a * (((x i : ℤ) : ℝ) * ((u : ℤ) : ℝ))) * (1 + b * (((u : ℤ) : ℝ) * ((z i : ℤ) : ℝ)))

lemma K_semi {n : ℕ} (a b : ℝ) (x z : Cube n) :
    ∑ y, K a x y * K b y z = (2:ℝ) ^ n * K (a * b) x z := by
  have e1 : ∀ y : Cube n, K a x y * K b y z = ∏ i, g2 a b x z i (y i) := by
    intro y
    unfold K g2
    rw [← Finset.prod_mul_distrib]
  have e2 : ∀ i : Fin n, ∑ u, g2 a b x z i u
      = 2 * (1 + (a * b) * (((x i : ℤ) : ℝ) * ((z i : ℤ) : ℝ))) := by
    intro i
    rw [sum_units]
    unfold g2
    simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]
    ring
  calc ∑ y, K a x y * K b y z = ∑ y : Cube n, ∏ i, g2 a b x z i (y i) :=
        Finset.sum_congr rfl (fun y _ => e1 y)
    _ = ∏ i, ∑ u, g2 a b x z i u := sum_prod_cube (g2 a b x z)
    _ = ∏ i : Fin n, (2 * (1 + (a * b) * (((x i : ℤ) : ℝ) * ((z i : ℤ) : ℝ)))) :=
        Finset.prod_congr rfl (fun i _ => e2 i)
    _ = (2:ℝ) ^ n * K (a * b) x z := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rfl

lemma T_comp {n : ℕ} (a b : ℝ) (h : Cube n → ℝ) (x : Cube n) :
    T a (T b h) x = T (a * b) h x := by
  have hN : ((2:ℝ) ^ n) ≠ 0 := by positivity
  have hK : ∀ z, K (a * b) x z = ((2:ℝ) ^ n)⁻¹ * ∑ y, K a x y * K b y z := by
    intro z
    rw [K_semi, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  unfold T
  simp only [hK, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun y _ => ?_))
  ring

lemma T_selfadj {n : ℕ} (a : ℝ) (g f : Cube n → ℝ) :
    ∑ x, g x * T a f x = ∑ x, T a g x * f x := by
  unfold T
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [K_comm a y x]
  ring

lemma T_one {n : ℕ} (a : ℝ) (x : Cube n) : T a (fun _ => (1:ℝ)) x = 1 := by
  unfold T
  simp only [one_mul]
  rw [K_sum]
  exact inv_mul_cancel₀ (by positivity)

lemma T_sum {n : ℕ} (a : ℝ) (f : Cube n → ℝ) : ∑ x, T a f x = ∑ x, f x := by
  calc ∑ x, T a f x = ∑ x, (fun _ => (1:ℝ)) x * T a f x := by simp
    _ = ∑ x, T a (fun _ => (1:ℝ)) x * f x := T_selfadj a _ f
    _ = ∑ x, f x := by simp only [T_one, one_mul]

lemma noise_eq {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) (x : Cube n) : noise ρ f x = T ρ f x := by
  have hK : ∀ y : Cube n, K ρ x y = ∑ S : Finset (Fin n),
      ρ ^ S.card * ((∏ j ∈ S, ((y j : ℤ) : ℝ)) * ∏ j ∈ S, ((x j : ℤ) : ℝ)) := by
    intro y
    unfold K
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_mul_distrib]
    ring
  simp only [noise, PSDPolyApprox.fourierCoeff, expect, chi, T, hK, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun S _ => ?_))
  ring

/-! ### Two-point inequality for even exponents -/

lemma sum_range_even_odd (φ : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range (2 * m + 1), φ j
      = ∑ k ∈ range (m + 1), φ (2 * k) + ∑ k ∈ range m, φ (2 * k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => φ (2 * k)) (m + 1),
      Finset.sum_range_succ (fun k => φ (2 * k + 1)) m, show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    ring

lemma even_binom (A c : ℝ) (m : ℕ) :
    (A + c) ^ (2 * m) + (A - c) ^ (2 * m) =
      2 * ∑ k ∈ range (m + 1), (c ^ 2) ^ k * (A ^ 2) ^ (m - k) * ((2 * m).choose (2 * k) : ℝ) := by
  have h1 : (A + c) ^ (2 * m)
      = ∑ j ∈ range (2 * m + 1), c ^ j * A ^ (2 * m - j) * ((2 * m).choose j : ℝ) := by
    rw [add_comm A c]
    exact add_pow c A (2 * m)
  have h2 : (A - c) ^ (2 * m)
      = ∑ j ∈ range (2 * m + 1), (-c) ^ j * A ^ (2 * m - j) * ((2 * m).choose j : ℝ) := by
    rw [sub_eq_add_neg, add_comm A (-c)]
    exact add_pow (-c) A (2 * m)
  rw [h1, h2, ← Finset.sum_add_distrib, sum_range_even_odd, Finset.mul_sum]
  have hodd : ∀ k ∈ range m, (c ^ (2 * k + 1) * A ^ (2 * m - (2 * k + 1))
        * ((2 * m).choose (2 * k + 1) : ℝ)
      + (-c) ^ (2 * k + 1) * A ^ (2 * m - (2 * k + 1)) * ((2 * m).choose (2 * k + 1) : ℝ)) = 0 := by
    intro k _
    rw [Odd.neg_pow (odd_two_mul_add_one k)]
    ring
  rw [Finset.sum_eq_zero hodd, add_zero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Even.neg_pow (even_two_mul k), show 2 * m - 2 * k = 2 * (m - k) by omega]
  simp only [pow_mul]
  ring

def D (k : ℕ) : ℕ := ∏ j ∈ range k, (2 * j + 1)

lemma D_pos (k : ℕ) : 0 < D k := Finset.prod_pos (fun j _ => by omega)

lemma fact_two_mul (k : ℕ) : (2 * k).factorial = 2 ^ k * k.factorial * D k := by
  induction k with
  | zero => simp [D]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, ih,
      Nat.factorial_succ k]
    unfold D
    rw [Finset.prod_range_succ]
    ring

lemma choose_D (m k : ℕ) (hk : k ≤ m) :
    (2 * m).choose (2 * k) * D k * D (m - k) = m.choose k * D m := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * m by omega)
  have e2 := Nat.choose_mul_factorial_mul_factorial hk
  rw [show 2 * m - 2 * k = 2 * (m - k) by omega, fact_two_mul, fact_two_mul, fact_two_mul] at e1
  have hpow : 2 ^ k * 2 ^ (m - k) = 2 ^ m := by
    rw [← pow_add]; congr 1; omega
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ m * k.factorial * (m - k).factorial by positivity)
  calc 2 ^ m * k.factorial * (m - k).factorial * ((2 * m).choose (2 * k) * D k * D (m - k))
      = (2 * m).choose (2 * k) * (2 ^ k * k.factorial * D k)
          * (2 ^ (m - k) * (m - k).factorial * D (m - k)) := by
        rw [← hpow]; ring
    _ = 2 ^ m * m.factorial * D m := e1
    _ = 2 ^ m * k.factorial * (m - k).factorial * (m.choose k * D m) := by
        rw [← e2]; ring

lemma D_le (m k : ℕ) (hk : k ≤ m) : D m ≤ D (m - k) * (2 * m - 1) ^ k := by
  have e : D m = D (m - k) * ∏ i ∈ range k, (2 * (m - k + i) + 1) := by
    have := Finset.prod_range_add (fun j => 2 * j + 1) (m - k) k
    rw [Nat.sub_add_cancel hk] at this
    exact this
  rw [e]
  apply Nat.mul_le_mul_left
  have := Finset.prod_le_pow_card (range k) (fun i => 2 * (m - k + i) + 1) (2 * m - 1)
    (fun i hi => by simp only [Finset.mem_range] at hi; omega)
  simpa using this

lemma coef (m k : ℕ) (hk : k ≤ m) : (2 * m).choose (2 * k) ≤ m.choose k * (2 * m - 1) ^ k := by
  have h1 := choose_D m k hk
  have h2 := D_le m k hk
  have hDk := D_pos k
  have hDmk := D_pos (m - k)
  have h3 : (2 * m).choose (2 * k) * D k * D (m - k) ≤ m.choose k * (2 * m - 1) ^ k * D (m - k) := by
    rw [h1]
    calc m.choose k * D m ≤ m.choose k * (D (m - k) * (2 * m - 1) ^ k) := Nat.mul_le_mul_left _ h2
      _ = m.choose k * (2 * m - 1) ^ k * D (m - k) := by ring
  have h4 := le_of_mul_le_mul_right h3 hDmk
  calc (2 * m).choose (2 * k) = (2 * m).choose (2 * k) * 1 := (mul_one _).symm
    _ ≤ (2 * m).choose (2 * k) * D k := Nat.mul_le_mul_left _ hDk
    _ ≤ m.choose k * (2 * m - 1) ^ k := h4

lemma two_point (m : ℕ) (hm : 1 ≤ m) (a A B : ℝ) (ha : a ^ 2 * (2 * (m:ℝ) - 1) ≤ 1) :
    (A + a * B) ^ (2 * m) + (A - a * B) ^ (2 * m) ≤ 2 * (A ^ 2 + B ^ 2) ^ m := by
  rw [even_binom]
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hc : (2 * (m:ℝ) - 1) * (a * B) ^ 2 ≤ B ^ 2 := by
    have := mul_le_mul_of_nonneg_right ha (sq_nonneg B)
    nlinarith [this]
  have hcast : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  calc 2 * ∑ k ∈ range (m + 1), ((a * B) ^ 2) ^ k * (A ^ 2) ^ (m - k) * ((2 * m).choose (2 * k) : ℝ)
      ≤ 2 * ∑ k ∈ range (m + 1),
          ((2 * (m:ℝ) - 1) * (a * B) ^ 2) ^ k * (A ^ 2) ^ (m - k) * (m.choose k : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hco0 := coef m k hk'
        have hco1 : ((2 * m).choose (2 * k) : ℝ) ≤ ((m.choose k * (2 * m - 1) ^ k : ℕ) : ℝ) := by
          exact_mod_cast hco0
        rw [Nat.cast_mul, Nat.cast_pow, hcast] at hco1
        have h0 : 0 ≤ ((a * B) ^ 2) ^ k * (A ^ 2) ^ (m - k) := by positivity
        calc ((a * B) ^ 2) ^ k * (A ^ 2) ^ (m - k) * ((2 * m).choose (2 * k) : ℝ)
            ≤ ((a * B) ^ 2) ^ k * (A ^ 2) ^ (m - k) * ((m.choose k : ℝ) * (2 * (m:ℝ) - 1) ^ k) :=
              mul_le_mul_of_nonneg_left hco1 h0
          _ = ((2 * (m:ℝ) - 1) * (a * B) ^ 2) ^ k * (A ^ 2) ^ (m - k) * (m.choose k : ℝ) := by
              rw [mul_pow (2 * (m:ℝ) - 1)]; ring
    _ = 2 * ((2 * (m:ℝ) - 1) * (a * B) ^ 2 + A ^ 2) ^ m := by
        rw [add_pow]
    _ ≤ 2 * (A ^ 2 + B ^ 2) ^ m := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_left₀ (add_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _))
          (by linarith) m

/-! ### Minkowski for natural powers with weights -/

lemma mink {ι : Type*} (s : Finset ι) (w F G : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hF : ∀ i, 0 ≤ F i)
    (hG : ∀ i, 0 ≤ G i) (m : ℕ) (hm : 1 ≤ m) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : ∑ i ∈ s, w i * F i ^ m ≤ α ^ m) (h2 : ∑ i ∈ s, w i * G i ^ m ≤ β ^ m) :
    ∑ i ∈ s, w i * (F i + G i) ^ m ≤ (α + β) ^ m := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨r, hr_def⟩ : ∃ r : ι → ℝ, r = fun i => w i ^ ((m:ℝ)⁻¹) := ⟨_, rfl⟩
  have hr0 : ∀ i, 0 ≤ r i := fun i => by rw [hr_def]; exact Real.rpow_nonneg (hw i) _
  have hr : ∀ i, r i ^ m = w i := fun i => by rw [hr_def]; exact Real.rpow_inv_natCast_pow (hw i) hm0
  have key : ∀ H : ι → ℝ, (∀ i, 0 ≤ H i) → ∀ i, |r i * H i| ^ (m:ℝ) = w i * H i ^ m := by
    intro H hH i
    rw [abs_of_nonneg (mul_nonneg (hr0 i) (hH i)), Real.rpow_natCast, mul_pow, hr]
  have L := Real.Lp_add_le s (fun i => r i * F i) (fun i => r i * G i) (p := (m:ℝ))
    (by exact_mod_cast hm)
  have e1 : ∑ i ∈ s, |r i * F i + r i * G i| ^ (m:ℝ) = ∑ i ∈ s, w i * (F i + G i) ^ m := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_add]
    exact key (fun i => F i + G i) (fun i => add_nonneg (hF i) (hG i)) i
  have e2 : ∑ i ∈ s, |r i * F i| ^ (m:ℝ) = ∑ i ∈ s, w i * F i ^ m :=
    Finset.sum_congr rfl (fun i _ => key F hF i)
  have e3 : ∑ i ∈ s, |r i * G i| ^ (m:ℝ) = ∑ i ∈ s, w i * G i ^ m :=
    Finset.sum_congr rfl (fun i _ => key G hG i)
  rw [e1, e2, e3] at L
  have hS0 : 0 ≤ ∑ i ∈ s, w i * (F i + G i) ^ m :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (pow_nonneg (add_nonneg (hF i) (hG i)) _))
  have hA : (∑ i ∈ s, w i * F i ^ m) ^ (1 / (m:ℝ)) ≤ α := by
    calc (∑ i ∈ s, w i * F i ^ m) ^ (1 / (m:ℝ)) ≤ (α ^ m) ^ (1 / (m:ℝ)) :=
          Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (pow_nonneg (hF i) _)))
            h1 (by positivity)
      _ = α := by rw [one_div]; exact Real.pow_rpow_inv_natCast hα hm0
  have hB : (∑ i ∈ s, w i * G i ^ m) ^ (1 / (m:ℝ)) ≤ β := by
    calc (∑ i ∈ s, w i * G i ^ m) ^ (1 / (m:ℝ)) ≤ (β ^ m) ^ (1 / (m:ℝ)) :=
          Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (pow_nonneg (hG i) _)))
            h2 (by positivity)
      _ = β := by rw [one_div]; exact Real.pow_rpow_inv_natCast hβ hm0
  calc ∑ i ∈ s, w i * (F i + G i) ^ m
      = ((∑ i ∈ s, w i * (F i + G i) ^ m) ^ (1 / (m:ℝ))) ^ m := by
        rw [one_div]; exact (Real.rpow_inv_natCast_pow hS0 hm0).symm
    _ ≤ (α + β) ^ m := pow_le_pow_left₀ (Real.rpow_nonneg hS0 _) (L.trans (add_le_add hA hB)) m

/-! ### Hypercontractivity `2 → 2m` by tensorisation -/

lemma K_cons {n : ℕ} (a : ℝ) (u v : ℤˣ) (x y : Cube n) :
    K a (Fin.cons u x : Cube (n + 1)) (Fin.cons v y)
      = (1 + a * (((u : ℤ) : ℝ) * ((v : ℤ) : ℝ))) * K a x y := by
  unfold K
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma sum_cube_succ {n : ℕ} (F : Cube (n + 1) → ℝ) :
    ∑ x, F x = ∑ u : ℤˣ, ∑ x : Cube n, F (Fin.cons u x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ℤˣ)) _ _ (fun p => rfl)).symm

noncomputable def h0f {n : ℕ} (h : Cube (n + 1) → ℝ) : Cube n → ℝ :=
  fun y => (h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2

noncomputable def h1f {n : ℕ} (h : Cube (n + 1) → ℝ) : Cube n → ℝ :=
  fun y => (h (Fin.cons 1 y) - h (Fin.cons (-1) y)) / 2

lemma T_cons {n : ℕ} (a : ℝ) (h : Cube (n + 1) → ℝ) (u : ℤˣ) (x : Cube n) :
    T a h (Fin.cons u x) = T a (h0f h) x + a * ((u : ℤ) : ℝ) * T a (h1f h) x := by
  unfold T h0f h1f
  rw [sum_cube_succ, sum_units]
  simp only [K_cons, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]
  rw [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

theorem HC (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : a ^ 2 * (2 * (m:ℝ) - 1) ≤ 1) :
    ∀ (n : ℕ) (h : Cube n → ℝ),
      ((2:ℝ) ^ n)⁻¹ * ∑ x, (T a h x) ^ (2 * m) ≤ (((2:ℝ) ^ n)⁻¹ * ∑ x, (h x) ^ 2) ^ m := by
  intro n
  induction n with
  | zero =>
    intro h
    have hT : ∀ x : Cube 0, T a h x = h x := by
      intro x
      unfold T K
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      congr 1
      exact Subsingleton.elim _ _
    simp only [hT, pow_zero, inv_one, one_mul, Fintype.sum_unique]
    rw [← pow_mul]
  | succ n ih =>
    intro h
    have hdec := T_cons a h
    have hsplit : ∑ x : Cube (n + 1), (T a h x) ^ (2 * m) =
        ∑ x : Cube n, ((T a (h0f h) x + a * T a (h1f h) x) ^ (2 * m)
          + (T a (h0f h) x - a * T a (h1f h) x) ^ (2 * m)) := by
      rw [sum_cube_succ, sum_units, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have e1 : T a h (Fin.cons 1 x) = T a (h0f h) x + a * T a (h1f h) x := by
        rw [hdec]; simp only [Units.val_one, Int.cast_one]; ring
      have e2 : T a h (Fin.cons (-1) x) = T a (h0f h) x - a * T a (h1f h) x := by
        rw [hdec]; simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]; ring
      rw [e1, e2]
    have hsq : ∑ x : Cube (n + 1), (h x) ^ 2
        = 2 * ∑ x : Cube n, ((h0f h x) ^ 2 + (h1f h x) ^ 2) := by
      rw [sum_cube_succ, sum_units, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [h0f, h1f]
      ring
    have htp : ∀ x : Cube n, (T a (h0f h) x + a * T a (h1f h) x) ^ (2 * m)
        + (T a (h0f h) x - a * T a (h1f h) x) ^ (2 * m)
        ≤ 2 * ((T a (h0f h) x) ^ 2 + (T a (h1f h) x) ^ 2) ^ m :=
      fun x => two_point m hm a _ _ ha
    have ih0 := ih (h0f h)
    have ih1 := ih (h1f h)
    have hM := mink Finset.univ (fun _ => ((2:ℝ) ^ n)⁻¹) (fun x => (T a (h0f h) x) ^ 2)
      (fun x => (T a (h1f h) x) ^ 2)
      (fun _ => inv_nonneg.2 (pow_nonneg (by norm_num) _)) (fun x => sq_nonneg _)
      (fun x => sq_nonneg _) m hm
      (((2:ℝ) ^ n)⁻¹ * ∑ x, (h0f h x) ^ 2) (((2:ℝ) ^ n)⁻¹ * ∑ x, (h1f h x) ^ 2)
      (by positivity) (by positivity)
      (by
        show ∑ x, ((2:ℝ) ^ n)⁻¹ * ((T a (h0f h) x) ^ 2) ^ m
          ≤ (((2:ℝ) ^ n)⁻¹ * ∑ x, (h0f h x) ^ 2) ^ m
        rw [← Finset.mul_sum]
        simp only [← pow_mul]
        exact ih0)
      (by
        show ∑ x, ((2:ℝ) ^ n)⁻¹ * ((T a (h1f h) x) ^ 2) ^ m
          ≤ (((2:ℝ) ^ n)⁻¹ * ∑ x, (h1f h x) ^ 2) ^ m
        rw [← Finset.mul_sum]
        simp only [← pow_mul]
        exact ih1)
    calc ((2:ℝ) ^ (n + 1))⁻¹ * ∑ x, (T a h x) ^ (2 * m)
        = ((2:ℝ) ^ (n + 1))⁻¹ * ∑ x : Cube n, ((T a (h0f h) x + a * T a (h1f h) x) ^ (2 * m)
          + (T a (h0f h) x - a * T a (h1f h) x) ^ (2 * m)) := by rw [hsplit]
      _ ≤ ((2:ℝ) ^ (n + 1))⁻¹ * ∑ x : Cube n,
            2 * ((T a (h0f h) x) ^ 2 + (T a (h1f h) x) ^ 2) ^ m :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => htp x)) (by positivity)
      _ = ∑ x : Cube n, ((2:ℝ) ^ n)⁻¹ * ((T a (h0f h) x) ^ 2 + (T a (h1f h) x) ^ 2) ^ m := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          ring
      _ ≤ (((2:ℝ) ^ n)⁻¹ * ∑ x, (h0f h x) ^ 2 + ((2:ℝ) ^ n)⁻¹ * ∑ x, (h1f h x) ^ 2) ^ m := hM
      _ = (((2:ℝ) ^ (n + 1))⁻¹ * ∑ x, (h x) ^ 2) ^ m := by
          rw [hsq]
          congr 1
          rw [Finset.sum_add_distrib]
          ring

/-! ### The `(1 + 1/(2m-1)) → 2` bound for bounded nonnegative functions -/

lemma jensen_sum {ι : Type*} [Fintype ι] (f H : ι → ℝ) (hf : ∀ x, 0 ≤ f x) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x, f x ≤ L) (k : ℕ) (hk : 1 ≤ k) :
    (∑ x, f x * |H x|) ^ k ≤ (∑ x, f x) ^ (k - 1) * L * ∑ x, |H x| ^ k := by
  have hS0 : 0 ≤ ∑ x, f x := Finset.sum_nonneg (fun x _ => hf x)
  rcases hS0.eq_or_lt with h0 | hpos
  · have hz : ∀ x, f x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hf x)).1 h0.symm x (Finset.mem_univ x)
    simp only [hz, zero_mul, Finset.sum_const_zero]
    rw [zero_pow (show k ≠ 0 by omega)]
    exact mul_nonneg (mul_nonneg (pow_nonneg le_rfl _) hL0)
      (Finset.sum_nonneg (fun x _ => by positivity))
  · have hSne : (∑ x, f x) ≠ 0 := hpos.ne'
    have hw := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun x => f x / ∑ y, f y)
      (fun x => |H x|) (fun x _ => div_nonneg (hf x) hpos.le)
      (by
        show ∑ x, f x / ∑ y, f y = 1
        rw [← Finset.sum_div, div_self hSne])
      (fun x _ => abs_nonneg _) k
    have e1 : ∑ x, f x * |H x| = (∑ y, f y) * ∑ x, f x / (∑ y, f y) * |H x| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [show (∑ y, f y) * (f x / (∑ y, f y) * |H x|) = f x * |H x| * ((∑ y, f y) / (∑ y, f y))
        by ring, div_self hSne, mul_one]
    have e2 : ∑ x, f x / (∑ y, f y) * |H x| ^ k ≤ L / (∑ y, f y) * ∑ x, |H x| ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hL x) hpos.le) (by positivity))
    rw [e1, mul_pow]
    have hk1 : (∑ y, f y) ^ k = (∑ y, f y) ^ (k - 1) * (∑ y, f y) := by
      rw [← pow_succ]; congr 1; omega
    calc (∑ y, f y) ^ k * (∑ x, f x / (∑ y, f y) * |H x|) ^ k
        ≤ (∑ y, f y) ^ k * (L / (∑ y, f y) * ∑ x, |H x| ^ k) :=
          mul_le_mul_of_nonneg_left (hw.trans e2) (pow_nonneg hpos.le k)
      _ = (∑ y, f y) ^ (k - 1) * L * (∑ x, |H x| ^ k) * ((∑ y, f y) / (∑ y, f y)) := by
          rw [hk1]; ring
      _ = (∑ y, f y) ^ (k - 1) * L * ∑ x, |H x| ^ k := by rw [div_self hSne, mul_one]

lemma L2bound {n : ℕ} (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : a ^ 2 * (2 * (m:ℝ) - 1) ≤ 1)
    (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) (L : ℝ) (hL : ∀ x, f x ≤ L) :
    (((2:ℝ) ^ n)⁻¹ * ∑ x, (T a f x) ^ 2) ^ m ≤ (((2:ℝ) ^ n)⁻¹ * ∑ x, f x) ^ (2 * m - 1) * L := by
  have hN : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have hL0 : 0 ≤ L := le_trans (hf (fun _ => 1)) (hL _)
  obtain ⟨X, hX⟩ : ∃ X, X = ((2:ℝ) ^ n)⁻¹ * ∑ x, (T a f x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ((2:ℝ) ^ n)⁻¹ * ∑ x, f x := ⟨_, rfl⟩
  rw [← hX, ← hE]
  have hX0 : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg (fun x _ => sq_nonneg _))
  have hE0 : 0 ≤ E := by
    rw [hE]; exact mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg (fun x _ => hf x))
  have hSf : ∑ x, f x = (2:ℝ) ^ n * E := by
    rw [hE, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hSX : ∑ x, (T a f x) ^ 2 = (2:ℝ) ^ n * X := by
    rw [hX, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have h1 : ∑ x, (T a f x) ^ 2 = ∑ x, f x * T a (T a f) x := by
    have := T_selfadj a (T a f) f
    rw [show ∑ x, f x * T a (T a f) x = ∑ x, T a (T a f) x * f x from
      Finset.sum_congr rfl (fun x _ => mul_comm _ _), ← this]
    exact Finset.sum_congr rfl (fun x _ => sq _)
  have h2 : ∑ x, f x * T a (T a f) x ≤ ∑ x, f x * |T a (T a f) x| :=
    Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (le_abs_self _) (hf x))
  have h3 := jensen_sum f (T a (T a f)) hf L hL0 hL (2 * m) (by omega)
  have h4 : ∑ x, |T a (T a f) x| ^ (2 * m) = ∑ x, (T a (T a f) x) ^ (2 * m) :=
    Finset.sum_congr rfl (fun x _ => Even.pow_abs ⟨m, by ring⟩ _)
  have h5 := HC m hm a ha n (T a f)
  rw [← hX] at h5
  have hSH : ∑ x, (T a (T a f) x) ^ (2 * m) ≤ (2:ℝ) ^ n * X ^ m := by
    have := mul_le_mul_of_nonneg_left h5 hN.le
    rwa [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
  have hmain : ((2:ℝ) ^ n * X) ^ (2 * m) ≤ ((2:ℝ) ^ n * E) ^ (2 * m - 1) * L * ((2:ℝ) ^ n * X ^ m) := by
    rw [← hSX, ← hSf]
    calc (∑ x, (T a f x) ^ 2) ^ (2 * m) = (∑ x, f x * T a (T a f) x) ^ (2 * m) := by rw [h1]
      _ ≤ (∑ x, f x * |T a (T a f) x|) ^ (2 * m) :=
          pow_le_pow_left₀ (by rw [← h1]; positivity) h2 _
      _ ≤ (∑ x, f x) ^ (2 * m - 1) * L * ∑ x, |T a (T a f) x| ^ (2 * m) := h3
      _ ≤ (∑ x, f x) ^ (2 * m - 1) * L * ((2:ℝ) ^ n * X ^ m) := by
          rw [h4]
          exact mul_le_mul_of_nonneg_left hSH
            (mul_nonneg (pow_nonneg (Finset.sum_nonneg (fun x _ => hf x)) _) hL0)
  have hN2 : ((2:ℝ) ^ n) ^ (2 * m - 1) * (2:ℝ) ^ n = ((2:ℝ) ^ n) ^ (2 * m) := by
    rw [← pow_succ]; congr 1; omega
  have hmain' : ((2:ℝ) ^ n) ^ (2 * m) * (X ^ m * X ^ m)
      ≤ ((2:ℝ) ^ n) ^ (2 * m) * (E ^ (2 * m - 1) * L * X ^ m) := by
    have e1 : ((2:ℝ) ^ n * X) ^ (2 * m) = ((2:ℝ) ^ n) ^ (2 * m) * (X ^ m * X ^ m) := by
      rw [mul_pow, ← pow_add, ← two_mul]
    have e2 : ((2:ℝ) ^ n * E) ^ (2 * m - 1) * L * ((2:ℝ) ^ n * X ^ m)
        = ((2:ℝ) ^ n) ^ (2 * m) * (E ^ (2 * m - 1) * L * X ^ m) := by
      rw [← hN2, mul_pow]; ring
    rw [← e1, ← e2]
    exact hmain
  have hfin : X ^ m * X ^ m ≤ E ^ (2 * m - 1) * L * X ^ m :=
    le_of_mul_le_mul_left hmain' (by positivity)
  have hY0 : 0 ≤ X ^ m := pow_nonneg hX0 m
  have hZ0 : 0 ≤ E ^ (2 * m - 1) * L := mul_nonneg (pow_nonneg hE0 _) hL0
  nlinarith [mul_nonneg hZ0 hY0, hfin]

/-! ### Main argument -/

theorem main (β t : ℝ) (hβ : 0 < β) (ht : Real.exp 1 < t) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f : Cube n → ℝ), (∀ x, 0 ≤ f x) → expect f = 1 →
      (∀ x, f x ≤ Real.exp (Real.sqrt n)) →
      prob {x | t ≤ noise (Real.sqrt (β / (n : ℝ))) f x} ≤ Real.exp (-(c * Real.sqrt n)) := by
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 = ⌈144 * β ^ 2⌉₊ + 1 := ⟨_, rfl⟩
  have hN0pos : (0:ℝ) < N0 := by rw [hN0]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((2:ℝ) ^ N0)⁻¹ := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (1 / (12 * β)) (δ / Real.sqrt N0) := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hc]; exact lt_min (by positivity) (div_pos hδpos (Real.sqrt_pos.2 hN0pos))
  refine ⟨c, hcpos, ?_⟩
  intro n f hf hEf hM
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.sqrt (β / (n : ℝ)) := ⟨_, rfl⟩
  rw [← hρ]
  have hN : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have ht1 : 1 < t := by linarith [Real.add_one_le_exp (1:ℝ)]
  have ht0 : 0 < t := by linarith
  -- probability as an average of an indicator
  have hprob : prob {x | t ≤ noise ρ f x}
      = ((2:ℝ) ^ n)⁻¹ * ∑ x, (if t ≤ T ρ f x then (1:ℝ) else 0) := by
    unfold prob
    have hset : {x | t ≤ noise ρ f x}
        = ((Finset.univ.filter (fun x => t ≤ T ρ f x) : Finset (Cube n)) : Set (Cube n)) := by
      ext x; simp [noise_eq]
    rw [hset, Set.ncard_coe_finset, Finset.card_filter]
    push_cast
    ring
  rw [hprob]
  obtain ⟨g, hg⟩ : ∃ g : Cube n → ℝ, g = fun x => if t ≤ T ρ f x then (1:ℝ) else 0 := ⟨_, rfl⟩
  rw [show (∑ x, (if t ≤ T ρ f x then (1:ℝ) else 0)) = ∑ x, g x by rw [hg]]
  have hg0 : ∀ x, 0 ≤ g x := by intro x; rw [hg]; dsimp only; split_ifs <;> norm_num
  have hg1 : ∀ x, g x ≤ 1 := by intro x; rw [hg]; dsimp only; split_ifs <;> norm_num
  have hSf : ∑ x, f x = (2:ℝ) ^ n := by
    have h := hEf
    unfold expect at h
    calc ∑ x, f x = (2:ℝ) ^ n * (((2:ℝ) ^ n)⁻¹ * ∑ x, f x) := by
          rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
      _ = (2:ℝ) ^ n := by rw [h, mul_one]
  have hcard : ∑ _y : Cube n, (1:ℝ) = (2:ℝ) ^ n := by
    rw [← K_sum (n := n) 0 (fun _ => (1:ℤˣ))]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    unfold K
    simp
  have hTsum : ∑ x, T ρ f x = (2:ℝ) ^ n := by rw [T_sum, hSf]
  have hμ0 : 0 ≤ ((2:ℝ) ^ n)⁻¹ * ∑ x, g x :=
    mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg (fun x _ => hg0 x))
  by_cases hn : n < N0
  · -- small n
    have hex : ∃ x0, ¬ (t ≤ T ρ f x0) := by
      by_contra hcon
      push_neg at hcon
      have h1 : ∑ _x : Cube n, t ≤ ∑ x, T ρ f x := Finset.sum_le_sum (fun x _ => hcon x)
      have h2 : ∑ _x : Cube n, t = t * (2:ℝ) ^ n := by
        rw [← hcard, Finset.mul_sum]; simp
      rw [h2, hTsum] at h1
      nlinarith
    obtain ⟨x0, hx0⟩ := hex
    have hsum : ∑ x, g x ≤ (2:ℝ) ^ n - 1 := by
      have h1 : ∑ x, (g x + if x = x0 then (1:ℝ) else 0) ≤ ∑ _x : Cube n, (1:ℝ) :=
        Finset.sum_le_sum (fun x _ => by
          by_cases hx : x = x0
          · subst hx
            simp [hg, hx0]
          · simp only [if_neg hx]
            linarith [hg1 x])
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', hcard] at h1
      simp only [Finset.mem_univ, ↓reduceIte] at h1
      linarith
    have hμ : ((2:ℝ) ^ n)⁻¹ * ∑ x, g x ≤ 1 - ((2:ℝ) ^ n)⁻¹ := by
      calc ((2:ℝ) ^ n)⁻¹ * ∑ x, g x ≤ ((2:ℝ) ^ n)⁻¹ * ((2:ℝ) ^ n - 1) :=
            mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hN.le)
        _ = 1 - ((2:ℝ) ^ n)⁻¹ := by rw [mul_sub, inv_mul_cancel₀ hN.ne', mul_one]
    have h2 : δ ≤ ((2:ℝ) ^ n)⁻¹ := by
      rw [hδ]; exact inv_anti₀ hN (pow_le_pow_right₀ (by norm_num) hn.le)
    have h3 : 1 - δ ≤ Real.exp (-δ) := by linarith [Real.add_one_le_exp (-δ)]
    have h4 : c * Real.sqrt n ≤ δ := by
      have hc2 : c ≤ δ / Real.sqrt N0 := by rw [hc]; exact min_le_right _ _
      have hsq : Real.sqrt n ≤ Real.sqrt N0 := Real.sqrt_le_sqrt (by exact_mod_cast hn.le)
      calc c * Real.sqrt n ≤ (δ / Real.sqrt N0) * Real.sqrt N0 :=
            mul_le_mul hc2 hsq (Real.sqrt_nonneg _) (div_pos hδpos (Real.sqrt_pos.2 hN0pos)).le
        _ = δ := div_mul_cancel₀ δ (ne_of_gt (Real.sqrt_pos.2 hN0pos))
    calc ((2:ℝ) ^ n)⁻¹ * ∑ x, g x ≤ 1 - ((2:ℝ) ^ n)⁻¹ := hμ
      _ ≤ 1 - δ := by linarith
      _ ≤ Real.exp (-δ) := h3
      _ ≤ Real.exp (-(c * Real.sqrt n)) := Real.exp_le_exp.2 (by linarith)
  · -- large n
    have hnN : N0 ≤ n := not_lt.mp hn
    have hn144 : 144 * β ^ 2 ≤ (n:ℝ) := by
      have h1 : 144 * β ^ 2 ≤ (⌈144 * β ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈144 * β ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by rw [← hN0]; exact_mod_cast hnN
      push_cast at h2
      linarith
    have hn1 : (1:ℝ) ≤ n := by
      have : (1:ℝ) ≤ N0 := by rw [hN0]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈144 * β ^ 2⌉₊]
      exact le_trans this (by exact_mod_cast hnN)
    have hnpos : (0:ℝ) < n := by linarith
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt n := ⟨_, rfl⟩
    rw [← hr]
    have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
    have hrsq : r ^ 2 = n := by rw [hr]; exact Real.sq_sqrt (Nat.cast_nonneg n)
    have hr1 : 1 ≤ r := by nlinarith [hrsq, hn1, hr0]
    have hr12 : 12 * β ≤ r := by nlinarith [hrsq, hn144, hr0, hβ, mul_pos hβ hβ]
    -- the two exponents
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈r⌉₊ := ⟨_, rfl⟩
    have hm_ge : r ≤ m := by rw [hmdef]; exact Nat.le_ceil r
    have hm_lt : (m:ℝ) < r + 1 := by rw [hmdef]; exact Nat.ceil_lt_add_one hr0
    have hm1 : 1 ≤ m := by
      have : (1:ℝ) ≤ m := le_trans hr1 hm_ge
      exact_mod_cast this
    obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = ⌊r / (6 * β)⌋₊ := ⟨_, rfl⟩
    have hs_le : (s:ℝ) ≤ r / (6 * β) := by rw [hsdef]; exact Nat.floor_le (by positivity)
    have hs_gt : r / (6 * β) < s + 1 := by rw [hsdef]; exact Nat.lt_floor_add_one _
    have h2le : (2:ℝ) ≤ r / (6 * β) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hs1 : 1 ≤ s := by
      rw [hsdef]; exact Nat.le_floor (by push_cast; linarith)
    have hs1' : (1:ℝ) ≤ s := by exact_mod_cast hs1
    have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
    -- the two noise parameters
    have h2m0 : (0:ℝ) < 2 * (m:ℝ) - 1 := by linarith
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt (2 * (m:ℝ) - 1) := ⟨_, rfl⟩
    have hqpos : 0 < q := by rw [hq]; exact Real.sqrt_pos.2 h2m0
    have hq2 : q ^ 2 = 2 * (m:ℝ) - 1 := by rw [hq]; exact Real.sq_sqrt h2m0.le
    obtain ⟨a, haq⟩ : ∃ a : ℝ, a = q⁻¹ := ⟨_, rfl⟩
    obtain ⟨b, hbq⟩ : ∃ b : ℝ, b = ρ * q := ⟨_, rfl⟩
    have ha : a ^ 2 * (2 * (m:ℝ) - 1) ≤ 1 := by
      rw [haq, inv_pow, hq2, inv_mul_cancel₀ h2m0.ne']
    have hρ2 : ρ ^ 2 = β / n := by rw [hρ]; exact Real.sq_sqrt (by positivity)
    have hb : b ^ 2 * (2 * (s:ℝ) - 1) ≤ 1 := by
      have hb2 : b ^ 2 = β / n * (2 * (m:ℝ) - 1) := by rw [hbq, mul_pow, hρ2, hq2]
      have e1 : (2 * (m:ℝ) - 1) ≤ 3 * r := by linarith
      have e2 : (2 * (s:ℝ) - 1) ≤ r / (3 * β) := by
        have h3 : r / (3 * β) = 2 * (r / (6 * β)) := by
          rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]; ring
        rw [h3]; linarith
      have e3 : (2 * (m:ℝ) - 1) * (2 * (s:ℝ) - 1) ≤ 3 * r * (r / (3 * β)) :=
        mul_le_mul e1 e2 (by linarith) (by positivity)
      have e4 : 3 * r * (r / (3 * β)) = r ^ 2 / β := by
        rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]; ring
      have e5 : (β / n) * ((2 * (m:ℝ) - 1) * (2 * (s:ℝ) - 1)) ≤ (β / n) * (r ^ 2 / β) :=
        mul_le_mul_of_nonneg_left (e3.trans (le_of_eq e4)) (by positivity)
      have e6 : (β / n) * (r ^ 2 / β) = 1 := by
        rw [hrsq, div_mul_div_comm, mul_comm β (n:ℝ), div_self (show (n:ℝ) * β ≠ 0 by positivity)]
      calc b ^ 2 * (2 * (s:ℝ) - 1) = (β / n) * ((2 * (m:ℝ) - 1) * (2 * (s:ℝ) - 1)) := by
            rw [hb2]; ring
        _ ≤ 1 := e5.trans (le_of_eq e6)
    have hab : b * a = ρ := by rw [hbq, haq, mul_assoc, mul_inv_cancel₀ hqpos.ne', mul_one]
    have hnoiseT : ∀ x, T b (T a f) x = T ρ f x := fun x => by rw [T_comp, hab]
    -- abbreviations
    obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ((2:ℝ) ^ n)⁻¹ * ∑ x, g x := ⟨_, rfl⟩
    rw [← hμ]
    rw [← hμ] at hμ0
    obtain ⟨Xf, hXf⟩ : ∃ Xf : ℝ, Xf = ((2:ℝ) ^ n)⁻¹ * ∑ x, (T a f x) ^ 2 := ⟨_, rfl⟩
    obtain ⟨Xg, hXg⟩ : ∃ Xg : ℝ, Xg = ((2:ℝ) ^ n)⁻¹ * ∑ x, (T b g x) ^ 2 := ⟨_, rfl⟩
    have hXf0 : 0 ≤ Xf := by rw [hXf]; positivity
    have hXg0 : 0 ≤ Xg := by rw [hXg]; positivity
    have hXf' : Xf ^ m ≤ Real.exp r := by
      have := L2bound m hm1 a ha f hf (Real.exp (Real.sqrt n)) hM
      rw [← hXf, show ((2:ℝ) ^ n)⁻¹ * ∑ x, f x = 1 from hEf, one_pow, one_mul, ← hr] at this
      exact this
    have hXg' : Xg ^ s ≤ μ ^ (2 * s - 1) := by
      have := L2bound s hs1 b hb g hg0 1 hg1
      rw [← hXg, ← hμ, mul_one] at this
      exact this
    -- t μ ≤ ⟨g, T_ρ f⟩
    have hA : ∀ x, t * g x ≤ g x * T ρ f x := by
      intro x; rw [hg]; dsimp only
      split_ifs with h
      · linarith
      · simp
    have h1 : t * ∑ x, g x ≤ ∑ x, g x * T ρ f x := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun x _ => hA x)
    have hsumA : t * μ ≤ ((2:ℝ) ^ n)⁻¹ * ∑ x, g x * T ρ f x := by
      rw [hμ]
      calc t * (((2:ℝ) ^ n)⁻¹ * ∑ x, g x) = ((2:ℝ) ^ n)⁻¹ * (t * ∑ x, g x) := by ring
        _ ≤ ((2:ℝ) ^ n)⁻¹ * ∑ x, g x * T ρ f x :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hN.le)
    have hI0 := T_selfadj b g (T a f)
    have hI : ∑ x, g x * T ρ f x = ∑ x, T b g x * T a f x := by
      rw [← hI0]
      exact Finset.sum_congr rfl (fun x _ => by rw [hnoiseT])
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => T b g x) (fun x => T a f x)
    have hCS : (t * μ) ^ 2 ≤ Xg * Xf := by
      calc (t * μ) ^ 2 ≤ (((2:ℝ) ^ n)⁻¹ * ∑ x, g x * T ρ f x) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg ht0.le hμ0) hsumA 2
        _ = (((2:ℝ) ^ n)⁻¹) ^ 2 * (∑ x, T b g x * T a f x) ^ 2 := by rw [hI, mul_pow]
        _ ≤ (((2:ℝ) ^ n)⁻¹) ^ 2 * ((∑ x, (T b g x) ^ 2) * ∑ x, (T a f x) ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
        _ = Xg * Xf := by rw [hXg, hXf]; ring
    -- final algebra
    have hmain : μ ≤ Real.exp (-(s:ℝ)) := by
      rcases hμ0.eq_or_lt with h0 | hμpos
      · rw [← h0]; exact (Real.exp_pos _).le
      have stepA : (t * μ) ^ (2 * m * s) ≤ (μ ^ (2 * s - 1)) ^ m * (Real.exp r) ^ s := by
        have a1 : ((t * μ) ^ 2) ^ m ≤ Xg ^ m * Real.exp r := by
          calc ((t * μ) ^ 2) ^ m ≤ (Xg * Xf) ^ m := pow_le_pow_left₀ (sq_nonneg _) hCS m
            _ = Xg ^ m * Xf ^ m := mul_pow _ _ _
            _ ≤ Xg ^ m * Real.exp r := mul_le_mul_of_nonneg_left hXf' (pow_nonneg hXg0 m)
        have a2 : (((t * μ) ^ 2) ^ m) ^ s ≤ (Xg ^ m * Real.exp r) ^ s :=
          pow_le_pow_left₀ (pow_nonneg (sq_nonneg _) _) a1 s
        calc (t * μ) ^ (2 * m * s) = (((t * μ) ^ 2) ^ m) ^ s := by
              rw [← pow_mul, ← pow_mul, mul_assoc]
          _ ≤ (Xg ^ m * Real.exp r) ^ s := a2
          _ = (Xg ^ s) ^ m * (Real.exp r) ^ s := by
              rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m s]
          _ ≤ (μ ^ (2 * s - 1)) ^ m * (Real.exp r) ^ s :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg hXg0 s) hXg' m)
                (pow_nonneg (Real.exp_pos r).le s)
      have hK' : m + (2 * s - 1) * m = 2 * m * s := by
        zify [show 1 ≤ 2 * s by omega]; ring
      have stepB : (t * μ) ^ (2 * m * s) = t ^ (2 * m * s) * μ ^ m * μ ^ ((2 * s - 1) * m) := by
        rw [mul_pow, mul_assoc (t ^ (2 * m * s)), ← pow_add, hK']
      have stepC : (μ ^ (2 * s - 1)) ^ m = μ ^ ((2 * s - 1) * m) := (pow_mul _ _ _).symm
      have hP : 0 < μ ^ ((2 * s - 1) * m) := pow_pos hμpos _
      have stepD : t ^ (2 * m * s) * μ ^ m ≤ (Real.exp r) ^ s := by
        have h' := stepA
        rw [stepB, stepC] at h'
        have h'' : (t ^ (2 * m * s) * μ ^ m) * μ ^ ((2 * s - 1) * m)
            ≤ (Real.exp r) ^ s * μ ^ ((2 * s - 1) * m) := by linarith [h']
        exact le_of_mul_le_mul_right h'' hP
      have stepE : Real.exp ((2 * m * s : ℕ) : ℝ) * μ ^ m ≤ Real.exp ((s:ℝ) * m) := by
        calc Real.exp ((2 * m * s : ℕ) : ℝ) * μ ^ m = (Real.exp 1) ^ (2 * m * s) * μ ^ m := by
              rw [Real.exp_one_pow]
          _ ≤ t ^ (2 * m * s) * μ ^ m :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos 1).le ht.le _)
                (pow_nonneg hμ0 m)
          _ ≤ (Real.exp r) ^ s := stepD
          _ = Real.exp ((s:ℝ) * r) := (Real.exp_nat_mul r s).symm
          _ ≤ Real.exp ((s:ℝ) * m) :=
              Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hm_ge (Nat.cast_nonneg s))
      have stepF : μ ^ m ≤ (Real.exp (-(s:ℝ))) ^ m := by
        rw [← Real.exp_nat_mul]
        have hpos := Real.exp_pos ((2 * m * s : ℕ) : ℝ)
        have h' : μ ^ m ≤ Real.exp ((s:ℝ) * m) / Real.exp ((2 * m * s : ℕ) : ℝ) := by
          rw [le_div_iff₀ hpos]; linarith [stepE]
        rw [← Real.exp_sub] at h'
        convert h' using 2
        push_cast
        ring
      exact le_of_pow_le_pow_left₀ (by omega) (Real.exp_pos _).le stepF
    have hcr : c * r ≤ s := by
      have hc1 : c ≤ 1 / (12 * β) := by rw [hc]; exact min_le_left _ _
      have e1 : c * r ≤ r / (12 * β) := by
        calc c * r ≤ 1 / (12 * β) * r := mul_le_mul_of_nonneg_right hc1 hr0
          _ = r / (12 * β) := by ring
      have e2 : 1 ≤ r / (12 * β) := by rw [le_div_iff₀ (by positivity)]; linarith
      have e3 : r / (6 * β) = 2 * (r / (12 * β)) := by
        rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]; ring
      linarith
    calc μ ≤ Real.exp (-(s:ℝ)) := hmain
      _ ≤ Real.exp (-(c * r)) := Real.exp_le_exp.2 (by linarith)

end Aux_L1G

end PSDPolyApprox

open PSDPolyApprox in
theorem solution (β t : ℝ) (hβ : 0 < β) (ht : Real.exp 1 < t) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f : Cube n → ℝ), (∀ x, 0 ≤ f x) → expect f = 1 →
      (∀ x, f x ≤ Real.exp (Real.sqrt n)) →
      prob {x | t ≤ noise (Real.sqrt (β / (n : ℝ))) f x} ≤
        Real.exp (-(c * Real.sqrt n)) :=
  PSDPolyApprox.Aux_L1G.main β t hβ ht
