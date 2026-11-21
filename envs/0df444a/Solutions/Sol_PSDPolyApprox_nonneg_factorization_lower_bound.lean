-- Prove2me | solution 1 for PSDPolyApprox.nonneg_factorization_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:32:26.766098+00:00
-- url     : https://prove2.me/submissions/89a9dd6f-9776-469d-ac01-a2e48d9cf5bf

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_PSDPolyApprox_slackSubmatrix

open ExtensionComplexity.TSP

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
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f : Cube n → ℝ), (∀ x, 0 ≤ f x) →
      ((2:ℝ) ^ n)⁻¹ * ∑ x, f x = 1 →
      (∀ x, f x ≤ Real.exp (Real.sqrt n)) →
      ((2:ℝ) ^ n)⁻¹ * ∑ x, (if t ≤ T (Real.sqrt (β / (n : ℝ))) f x then (1:ℝ) else 0)
        ≤ Real.exp (-(c * Real.sqrt n)) := by
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
  obtain ⟨g, hg⟩ : ∃ g : Cube n → ℝ, g = fun x => if t ≤ T ρ f x then (1:ℝ) else 0 := ⟨_, rfl⟩
  rw [show (∑ x, (if t ≤ T ρ f x then (1:ℝ) else 0)) = ∑ x, g x by rw [hg]]
  have hg0 : ∀ x, 0 ≤ g x := by intro x; rw [hg]; dsimp only; split_ifs <;> norm_num
  have hg1 : ∀ x, g x ≤ 1 := by intro x; rw [hg]; dsimp only; split_ifs <;> norm_num
  have hSf : ∑ x, f x = (2:ℝ) ^ n := by
    have h := hEf
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

/-! ### Nonnegative rank lower bound -/

lemma K_zero {n : ℕ} (x y : Cube n) : K 0 x y = 1 := by
  unfold K; simp

lemma T_zero {n : ℕ} (h : Cube n → ℝ) (x : Cube n) : T 0 h x = ((2:ℝ) ^ n)⁻¹ * ∑ y, h y := by
  unfold T; simp only [K_zero, mul_one]

lemma card_sum {n : ℕ} : ∑ _y : Cube n, (1:ℝ) = (2:ℝ) ^ n := by
  have := K_sum (n := n) 0 (fun _ => 1)
  simp only [K_zero] at this
  exact this

lemma unit_sq (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

lemma unit_abs (u : ℤˣ) : |((u : ℤ) : ℝ)| = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

noncomputable def gm {n : ℕ} (ρ : ℝ) (y : Cube n) (i j : Fin n) (k : Fin n) (u : ℤˣ) : ℝ :=
  (if k = i then ((u : ℤ) : ℝ) else 1) * (if k = j then ((u : ℤ) : ℝ) else 1)
    * (1 + ρ * (((y k : ℤ) : ℝ) * ((u : ℤ) : ℝ)))

lemma mom {n : ℕ} (ρ : ℝ) (y : Cube n) (i j : Fin n) :
    ∑ z : Cube n, ((z i : ℤ) : ℝ) * ((z j : ℤ) : ℝ) * K ρ y z
      = (2:ℝ) ^ n * (if i = j then 1 else ρ ^ 2 * (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ))) := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, mul_one]
    simp only [unit_sq, one_mul]
    exact K_sum ρ y
  · rw [if_neg hij]
    have e1 : ∀ z : Cube n, ((z i : ℤ) : ℝ) * ((z j : ℤ) : ℝ) * K ρ y z
        = ∏ k, gm ρ y i j k (z k) := by
      intro z
      unfold K gm
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
        Finset.prod_ite_eq']
      simp
    have e2 : ∀ k, ∑ u, gm ρ y i j k u
        = 2 * ((if k = i then ρ * ((y k : ℤ) : ℝ) else 1)
          * (if k = j then ρ * ((y k : ℤ) : ℝ) else 1)) := by
      intro k
      rw [sum_units]
      unfold gm
      by_cases hki : k = i
      · have hkj : ¬ k = j := fun h => hij (hki.symm.trans h)
        simp only [if_pos hki, if_neg hkj, Units.val_one, Units.val_neg, Int.cast_one,
          Int.cast_neg]
        ring
      · by_cases hkj : k = j
        · simp only [if_neg hki, if_pos hkj, Units.val_one, Units.val_neg, Int.cast_one,
            Int.cast_neg]
          ring
        · simp only [if_neg hki, if_neg hkj, Units.val_one, Units.val_neg, Int.cast_one,
            Int.cast_neg]
          ring
    calc ∑ z : Cube n, ((z i : ℤ) : ℝ) * ((z j : ℤ) : ℝ) * K ρ y z
        = ∑ z : Cube n, ∏ k, gm ρ y i j k (z k) := Finset.sum_congr rfl (fun z _ => e1 z)
      _ = ∏ k, ∑ u, gm ρ y i j k u := sum_prod_cube (gm ρ y i j)
      _ = ∏ k, 2 * ((if k = i then ρ * ((y k : ℤ) : ℝ) else 1)
            * (if k = j then ρ * ((y k : ℤ) : ℝ) else 1)) :=
          Finset.prod_congr rfl (fun k _ => e2 k)
      _ = (2:ℝ) ^ n * (ρ ^ 2 * (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
            Finset.prod_ite_eq', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          simp only [Finset.mem_univ, ↓reduceIte]
          ring

lemma T_qy {n : ℕ} (hn : 1 ≤ n) (ρ ε : ℝ) (y : Cube n) :
    T ρ (fun x => (1 - ε) * qy n y x + ε) y = (1 - ε) * (1 + ((n:ℝ) - 1) * ρ ^ 2) + ε := by
  have hn0 : (n:ℝ) ≠ 0 := by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN : ((2:ℝ) ^ n) ≠ 0 := by positivity
  have hsq : ∀ z : Cube n, (∑ i, ((z i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2 * K ρ y z
      = ∑ i, ∑ j, (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ))
          * (((z i : ℤ) : ℝ) * ((z j : ℤ) : ℝ) * K ρ y z) := by
    intro z
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hS2 : ∑ z : Cube n, (∑ i, ((z i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2 * K ρ y z
      = ∑ i, ∑ j, (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ))
          * ((2:ℝ) ^ n * (if i = j then 1 else ρ ^ 2 * (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ)))) := by
    rw [Finset.sum_congr rfl (fun z _ => hsq z), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum, mom]
  have hinner : ∀ i : Fin n, ∑ j, (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ))
      * ((2:ℝ) ^ n * (if i = j then 1 else ρ ^ 2 * (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ))))
      = (2:ℝ) ^ n * (1 + ((n:ℝ) - 1) * ρ ^ 2) := by
    intro i
    have e : ∀ j, (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ))
        * ((2:ℝ) ^ n * (if i = j then 1 else ρ ^ 2 * (((y i : ℤ) : ℝ) * ((y j : ℤ) : ℝ))))
        = (2:ℝ) ^ n * ρ ^ 2 + (if i = j then (2:ℝ) ^ n * (1 - ρ ^ 2) else 0) := by
      intro j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
        linear_combination (2:ℝ) ^ n * unit_sq (y i)
      · rw [if_neg hij, if_neg hij]
        linear_combination ((2:ℝ) ^ n * ρ ^ 2 * (((y j : ℤ) : ℝ) * ((y j : ℤ) : ℝ)))
          * unit_sq (y i) + ((2:ℝ) ^ n * ρ ^ 2) * unit_sq (y j)
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [Finset.mem_univ, ↓reduceIte, nsmul_eq_mul]
    ring
  unfold T qy
  calc ((2:ℝ) ^ n)⁻¹ * ∑ z, ((1 - ε) * ((n:ℝ)⁻¹ * (∑ i, ((z i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2)
          + ε) * K ρ y z
      = ((2:ℝ) ^ n)⁻¹ * ((1 - ε) * (n:ℝ)⁻¹
          * ∑ z : Cube n, (∑ i, ((z i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2 * K ρ y z
          + ε * ∑ z, K ρ y z) := by
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        ring
    _ = ((2:ℝ) ^ n)⁻¹ * ((1 - ε) * (n:ℝ)⁻¹ * ∑ i : Fin n, (2:ℝ) ^ n * (1 + ((n:ℝ) - 1) * ρ ^ 2)
          + ε * (2:ℝ) ^ n) := by
        rw [K_sum, hS2, Finset.sum_congr rfl (fun i _ => hinner i)]
    _ = (1 - ε) * (1 + ((n:ℝ) - 1) * ρ ^ 2) + ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : (n:ℝ)⁻¹ * n = 1 := inv_mul_cancel₀ hn0
        have h2 : ((2:ℝ) ^ n)⁻¹ * (2:ℝ) ^ n = 1 := inv_mul_cancel₀ hN
        linear_combination ((1 - ε) * (1 + ((n:ℝ) - 1) * ρ ^ 2) * (((2:ℝ) ^ n)⁻¹ * (2:ℝ) ^ n)) * h1
          + ((1 - ε) * (1 + ((n:ℝ) - 1) * ρ ^ 2) + ε) * h2

lemma T_lin {n N : ℕ} (ρ : ℝ) (A : Cube n → Fin N → ℝ) (B : Fin N → ℝ) (z : Cube n) :
    T ρ (fun x => ∑ l, A x l * B l) z = ∑ l, T ρ (fun x => A x l) z * B l := by
  unfold T
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun x _ => ?_))
  ring

lemma T_smul {n : ℕ} (ρ c : ℝ) (h : Cube n → ℝ) (z : Cube n) :
    T ρ (fun x => c * h x) z = c * T ρ h z := by
  simp only [T, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

lemma K_nonneg {n : ℕ} (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (x y : Cube n) : 0 ≤ K ρ x y := by
  unfold K
  refine Finset.prod_nonneg (fun i _ => ?_)
  rcases Int.units_eq_one_or (x i) with hx | hx <;> rcases Int.units_eq_one_or (y i) with hy | hy <;>
    simp only [hx, hy, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg] <;> nlinarith

lemma T_nonneg {n : ℕ} (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (h : Cube n → ℝ)
    (hh : ∀ x, 0 ≤ h x) (z : Cube n) : 0 ≤ T ρ h z := by
  unfold T
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun x _ => mul_nonneg (hh x) (K_nonneg ρ h0 h1 z x)))

set_option maxHeartbeats 1600000 in
theorem nfl (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ N : ℕ,
      HasNonnegFactorization (slackSubmatrix ε n) N → Real.exp (C * Real.sqrt n) ≤ N := by
  have hne : (1 - ε) ≠ 0 := by
    intro h; linarith
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 8 / (1 - ε) := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; exact div_pos (by norm_num) (by linarith)
  have hb8 : (1 - ε) * β = 8 := by rw [hβdef]; field_simp
  obtain ⟨c, hc0, hc⟩ := main β (7/2) hβ (by linarith [Real.exp_one_lt_d9])
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = min (1/2) c := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc']; exact lt_min (by norm_num) hc0
  have hc'1 : c' ≤ 1/2 := by rw [hc']; exact min_le_left _ _
  have hc'2 : c' ≤ c := by rw [hc']; exact min_le_right _ _
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℕ, n1 = ⌈β⌉₊ + 147456 := ⟨_, rfl⟩
  have hn1pos : (0:ℝ) < n1 := by rw [hn1]; positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = min (min (1/4) (c'/2)) (Real.log 2 / Real.sqrt n1) := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    rw [hC]
    exact lt_min (lt_min (by norm_num) (by linarith))
      (div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.2 hn1pos))
  have hC1 : C ≤ 1/4 := by rw [hC]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hC2 : C ≤ c'/2 := by rw [hC]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hC3 : C ≤ Real.log 2 / Real.sqrt n1 := by rw [hC]; exact min_le_right _ _
  refine ⟨C, hC0, ?_⟩
  intro n hn N hfac
  obtain ⟨A, B, hA, hB, hM⟩ := hfac
  have hn1' : 1 ≤ n := by omega
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hN2 : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have hMxy : ∀ x y, slackSubmatrix ε n x y = ∑ l, A x l * B l y := by
    intro x y; rw [hM, Matrix.mul_apply]
  have hMle : ∀ x y, slackSubmatrix ε n x y ≤ n := by
    intro x y
    unfold slackSubmatrix qy
    have hS : |∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)| ≤ n := by
      calc |∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)|
          ≤ ∑ i, |((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ _i : Fin n, (1:ℝ) :=
            Finset.sum_congr rfl (fun i _ => by rw [abs_mul, unit_abs, unit_abs, mul_one])
        _ = n := by simp
    have hS2 : (∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2 ≤ (n:ℝ) * n := by
      rw [← sq_abs, sq]
      exact mul_le_mul hS hS (abs_nonneg _) hnpos.le
    have hq : (n:ℝ)⁻¹ * (∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2 ≤ n := by
      rw [inv_mul_le_iff₀ hnpos]; exact hS2
    have h1ε : 0 ≤ 1 - ε := by linarith
    linarith [mul_le_mul_of_nonneg_left hq h1ε,
      mul_nonneg hε0.le (show (0:ℝ) ≤ n - 1 by linarith)]
  have hsym : ∀ x y, slackSubmatrix ε n x y = slackSubmatrix ε n y x := by
    intro x y
    unfold slackSubmatrix qy
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (((x i : ℤ) : ℝ)) (((y i : ℤ) : ℝ)))]
  obtain ⟨α, hα⟩ : ∃ α : Fin N → ℝ, α = fun l => ((2:ℝ) ^ n)⁻¹ * ∑ x, A x l := ⟨_, rfl⟩
  have hα0 : ∀ l, 0 ≤ α l := fun l => by
    rw [hα]; exact mul_nonneg (inv_nonneg.2 hN2.le) (Finset.sum_nonneg (fun x _ => hA x l))
  have hcol : ∀ ρ : ℝ, ∀ y : Cube n, ∑ l, T ρ (fun x => A x l) y * B l y
      = (1 - ε) * (1 + ((n:ℝ) - 1) * ρ ^ 2) + ε := by
    intro ρ y
    have hfun : (fun x => ∑ l, A x l * B l y) = (fun x => (1 - ε) * qy n y x + ε) := by
      funext x
      rw [← hMxy]
      rfl
    calc ∑ l, T ρ (fun x => A x l) y * B l y = T ρ (fun x => ∑ l, A x l * B l y) y :=
          (T_lin ρ (fun x l => A x l) (fun l => B l y) y).symm
      _ = T ρ (fun x => (1 - ε) * qy n y x + ε) y := by rw [hfun]
      _ = (1 - ε) * (1 + ((n:ℝ) - 1) * ρ ^ 2) + ε := T_qy hn1' ρ ε y
  have hsumα : ∀ y, ∑ l, α l * B l y = 1 := by
    intro y
    have h := hcol 0 y
    rw [show (1 - ε) * (1 + ((n:ℝ) - 1) * (0:ℝ) ^ 2) + ε = 1 by ring] at h
    rw [← h, hα]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [T_zero]
  by_cases hsmall : n < n1
  · -- small `n`: the matrix has nonnegative rank at least two
    have hN2' : 2 ≤ N := by
      by_contra hlt
      push_neg at hlt
      interval_cases N
      · have := hsumα (fun _ => 1)
        simp at this
      · obtain ⟨x1, hx1⟩ : ∃ x1 : Cube n, x1 = fun _ => 1 := ⟨_, rfl⟩
        have h1 : ∀ y, α 0 * B 0 y = 1 := fun y => by
          have := hsumα y
          simpa using this
        have hα00 : α 0 ≠ 0 := fun h => by
          have := h1 x1
          rw [h, zero_mul] at this
          exact zero_ne_one this
        have hB' : ∀ y, B 0 y = B 0 x1 := fun y =>
          mul_left_cancel₀ hα00 ((h1 y).trans (h1 x1).symm)
        have hconst : ∀ y, slackSubmatrix ε n x1 y = slackSubmatrix ε n x1 x1 := by
          intro y
          rw [hMxy, hMxy, Fin.sum_univ_one, Fin.sum_univ_one, hB' y]
        have hc1 : slackSubmatrix ε n x1 x1 = (1 - ε) * n + ε := by
          unfold slackSubmatrix qy
          rw [hx1]
          simp only [Units.val_one, Int.cast_one, mul_one, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          have h := inv_mul_cancel₀ hnpos.ne'
          linear_combination ((1 - ε) * (n:ℝ)) * h
        have h0 := T_qy hn1' 0 ε x1
        simp only [T_zero] at h0
        have hterm : ∀ y : Cube n, (1 - ε) * qy n x1 y + ε = (1 - ε) * n + ε := by
          intro y
          show slackSubmatrix ε n y x1 = _
          rw [hsym, hconst, hc1]
        simp only [hterm] at h0
        have hsc : ∑ _y : Cube n, ((1 - ε) * (n:ℝ) + ε) = ((1 - ε) * n + ε) * (2:ℝ) ^ n := by
          rw [← card_sum, Finset.mul_sum]; simp
        rw [hsc] at h0
        have h0' : (1 - ε) * (n:ℝ) + ε = 1 := by
          have h2 : ((2:ℝ) ^ n)⁻¹ * (((1 - ε) * n + ε) * (2:ℝ) ^ n) = (1 - ε) * n + ε := by
            rw [mul_comm, mul_assoc, mul_inv_cancel₀ hN2.ne', mul_one]
          rw [h2] at h0
          linarith
        linarith [mul_pos (sub_pos.2 hε1) (show (0:ℝ) < n - 1 by linarith)]
    have hCn : C * Real.sqrt n ≤ Real.log 2 := by
      have hsq : Real.sqrt n ≤ Real.sqrt n1 := Real.sqrt_le_sqrt (by exact_mod_cast hsmall.le)
      calc C * Real.sqrt n ≤ (Real.log 2 / Real.sqrt n1) * Real.sqrt n1 :=
            mul_le_mul hC3 hsq (Real.sqrt_nonneg _)
              (div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.2 hn1pos)).le
        _ = Real.log 2 := div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 hn1pos))
    calc Real.exp (C * Real.sqrt n) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hCn
      _ = 2 := Real.exp_log (by norm_num)
      _ ≤ N := by exact_mod_cast hN2'
  · -- large `n`
    have hnn1 : n1 ≤ n := not_lt.mp hsmall
    have hnβ : β ≤ n := by
      have h1 : β ≤ (⌈β⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈β⌉₊ + 147456 : ℕ) : ℝ) ≤ n := by rw [← hn1]; exact_mod_cast hnn1
      push_cast at h2
      linarith
    have hnbig : (147456:ℝ) ≤ n := by
      have h2 : ((⌈β⌉₊ + 147456 : ℕ) : ℝ) ≤ n := by rw [← hn1]; exact_mod_cast hnn1
      push_cast at h2
      linarith [Nat.cast_nonneg (α := ℝ) ⌈β⌉₊]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt n := ⟨_, rfl⟩
    have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
    have hrsq : r ^ 2 = n := by rw [hr]; exact Real.sq_sqrt (Nat.cast_nonneg n)
    have hr384 : 384 ≤ r := by
      rw [hr]
      exact Real.le_sqrt_of_sq_le ((by norm_num : (384:ℝ) ^ 2 = 147456).trans_le hnbig)
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.sqrt (β / (n:ℝ)) := ⟨_, rfl⟩
    have hρ0 : 0 ≤ ρ := by rw [hρ]; exact Real.sqrt_nonneg _
    have hρ2 : ρ ^ 2 = β / n := by rw [hρ]; exact Real.sq_sqrt (by positivity)
    have hρ1 : ρ ≤ 1 := by
      have : β / (n:ℝ) ≤ 1 := by rw [div_le_one hnpos]; exact hnβ
      calc ρ = Real.sqrt (β / (n:ℝ)) := hρ
        _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt this
        _ = 1 := Real.sqrt_one
    have hval : ∀ y, 5 ≤ ∑ l, T ρ (fun x => A x l) y * B l y := by
      intro y
      rw [hcol]
      have hq : (1:ℝ) / 2 ≤ ((n:ℝ) - 1) / n := by rw [le_div_iff₀ hnpos]; linarith
      have e : (1 - ε) * (1 + ((n:ℝ) - 1) * ρ ^ 2) + ε = 1 + (1 - ε) * β * (((n:ℝ) - 1) / n) := by
        rw [hρ2]; ring
      rw [e, hb8]
      linarith
    by_contra hlt
    push_neg at hlt
    rw [← hr] at hlt
    have hexp4 : (n:ℝ) ≤ Real.exp (r / 4) := by
      have h := Real.pow_div_factorial_le_exp (r / 4) (by positivity) 3
      have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [h6] at h
      rw [← hrsq]
      nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.2 hr384), h]
    have hN' : (N:ℝ) ≤ Real.exp (r / 4) :=
      hlt.le.trans (Real.exp_le_exp.2 (by
        have := mul_le_mul_of_nonneg_right hC1 hr0
        linarith))
    have hNsmall : (N:ℝ) * ((n:ℝ) * Real.exp (-(r / 2))) ≤ 1 := by
      calc (N:ℝ) * ((n:ℝ) * Real.exp (-(r / 2)))
          ≤ Real.exp (r / 4) * (Real.exp (r / 4) * Real.exp (-(r / 2))) :=
            mul_le_mul hN' (mul_le_mul_of_nonneg_right hexp4 (Real.exp_pos _).le)
              (by positivity) (by positivity)
        _ = 1 := by
            rw [← Real.exp_add, ← Real.exp_add, show r / 4 + (r / 4 + -(r / 2)) = 0 by ring,
              Real.exp_zero]
    -- normalised columns
    obtain ⟨f, hf⟩ : ∃ f : Fin N → Cube n → ℝ, f = fun l x => (α l)⁻¹ * A x l := ⟨_, rfl⟩
    have hG : ∀ l y, T ρ (f l) y = (α l)⁻¹ * T ρ (fun x => A x l) y := by
      intro l y; rw [hf]; exact T_smul ρ (α l)⁻¹ (fun x => A x l) y
    obtain ⟨ind, hind⟩ : ∃ ind : Fin N → Cube n → ℝ, ind = fun l y =>
        if 0 < α l then
          (if (∃ x, α l * Real.exp r < A x l) then
            (if Real.exp (r / 2) < T ρ (f l) y then (1:ℝ) else 0)
          else (if 7 / 2 ≤ T ρ (f l) y then (1:ℝ) else 0))
        else 0 := ⟨_, rfl⟩
    have hind01 : ∀ l y, ind l y = 0 ∨ ind l y = 1 := by
      intro l y; rw [hind]; dsimp only; split_ifs <;> simp
    have hind0 : ∀ l y, 0 ≤ ind l y := by
      intro l y; rcases hind01 l y with h | h <;> rw [h] <;> norm_num
    have hpt : ∀ y, 1 ≤ ∑ l, ind l y := by
      intro y
      by_contra hlt1
      push_neg at hlt1
      have hz : ∀ l, ind l y = 0 := by
        intro l
        rcases hind01 l y with h | h
        · exact h
        · exfalso
          have := Finset.single_le_sum (fun l' _ => hind0 l' y) (Finset.mem_univ l)
          rw [h] at this
          linarith
      have hterm : ∀ l, T ρ (fun x => A x l) y * B l y
          ≤ (n:ℝ) * Real.exp (-(r / 2)) + 7 / 2 * (α l * B l y) := by
        intro l
        have hαB0 : 0 ≤ α l * B l y := mul_nonneg (hα0 l) (hB l y)
        have hne0 : 0 ≤ (n:ℝ) * Real.exp (-(r / 2)) := mul_nonneg hnpos.le (Real.exp_pos _).le
        have h0 := hz l
        rw [hind] at h0
        dsimp only at h0
        by_cases hαl : 0 < α l
        · rw [if_pos hαl] at h0
          have hFeq : T ρ (fun x => A x l) y * B l y = T ρ (f l) y * (α l * B l y) := by
            have e : (α l)⁻¹ * T ρ (fun x => A x l) y * (α l * B l y)
                = T ρ (fun x => A x l) y * B l y * ((α l)⁻¹ * α l) := by ring
            rw [hG, e, inv_mul_cancel₀ hαl.ne', mul_one]
          by_cases hI : ∃ x, α l * Real.exp r < A x l
          · rw [if_pos hI] at h0
            have hGs : T ρ (f l) y ≤ Real.exp (r / 2) := by
              by_contra h'
              push_neg at h'
              rw [if_pos h'] at h0
              norm_num at h0
            obtain ⟨x0, hx0⟩ := hI
            have hMx : A x0 l * B l y ≤ n := by
              calc A x0 l * B l y ≤ ∑ l', A x0 l' * B l' y :=
                    Finset.single_le_sum (f := fun l' => A x0 l' * B l' y)
                      (fun l' _ => mul_nonneg (hA _ _) (hB _ _))
                      (Finset.mem_univ l)
                _ = slackSubmatrix ε n x0 y := (hMxy x0 y).symm
                _ ≤ n := hMle x0 y
            have hαB : α l * B l y * Real.exp r ≤ n := by
              calc α l * B l y * Real.exp r = (α l * Real.exp r) * B l y := by ring
                _ ≤ A x0 l * B l y := mul_le_mul_of_nonneg_right hx0.le (hB l y)
                _ ≤ n := hMx
            have he : Real.exp (r / 2) = Real.exp r * Real.exp (-(r / 2)) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [hFeq]
            calc T ρ (f l) y * (α l * B l y) ≤ Real.exp (r / 2) * (α l * B l y) :=
                  mul_le_mul_of_nonneg_right hGs hαB0
              _ = Real.exp (-(r / 2)) * (α l * B l y * Real.exp r) := by rw [he]; ring
              _ ≤ Real.exp (-(r / 2)) * n := mul_le_mul_of_nonneg_left hαB (Real.exp_pos _).le
              _ ≤ (n:ℝ) * Real.exp (-(r / 2)) + 7 / 2 * (α l * B l y) := by
                  linarith [mul_comm (Real.exp (-(r / 2))) (n:ℝ)]
          · rw [if_neg hI] at h0
            have hGs : T ρ (f l) y < 7 / 2 := by
              by_contra h'
              push_neg at h'
              rw [if_pos h'] at h0
              norm_num at h0
            rw [hFeq]
            calc T ρ (f l) y * (α l * B l y) ≤ 7 / 2 * (α l * B l y) :=
                  mul_le_mul_of_nonneg_right hGs.le hαB0
              _ ≤ (n:ℝ) * Real.exp (-(r / 2)) + 7 / 2 * (α l * B l y) := by linarith
        · have hαl0 : α l = 0 := le_antisymm (not_lt.mp hαl) (hα0 l)
          have hsum0 : ∑ x, A x l = 0 := by
            have h := hαl0
            rw [hα] at h
            dsimp only at h
            rcases mul_eq_zero.mp h with h' | h'
            · exact absurd h' (inv_ne_zero hN2.ne')
            · exact h'
          have hA0 : ∀ x, A x l = 0 := fun x =>
            (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hA x l)).1 hsum0 x (Finset.mem_univ x)
          have hT0 : T ρ (fun x => A x l) y = 0 := by
            unfold T; simp [hA0]
          rw [hT0, zero_mul]
          linarith
      have hsumt := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hterm l)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, hsumα y] at hsumt
      linarith [hval y, hNsmall]
    have hsum_ind : ∀ l, ((2:ℝ) ^ n)⁻¹ * ∑ y, ind l y ≤ Real.exp (-(c' * r)) := by
      intro l
      by_cases hαl : 0 < α l
      · have hfl0 : ∀ x, 0 ≤ f l x := fun x => by
          rw [hf]; exact mul_nonneg (inv_nonneg.2 hαl.le) (hA x l)
        have hEf : ((2:ℝ) ^ n)⁻¹ * ∑ x, f l x = 1 := by
          rw [hf]
          dsimp only
          rw [← Finset.mul_sum]
          calc ((2:ℝ) ^ n)⁻¹ * ((α l)⁻¹ * ∑ x, A x l)
              = (α l)⁻¹ * (((2:ℝ) ^ n)⁻¹ * ∑ x, A x l) := by ring
            _ = (α l)⁻¹ * α l := by rw [hα]
            _ = 1 := inv_mul_cancel₀ hαl.ne'
        by_cases hI : ∃ x, α l * Real.exp r < A x l
        · have hpt2 : ∀ y, ind l y ≤ T ρ (f l) y / Real.exp (r / 2) := by
            intro y
            rw [hind]
            dsimp only
            rw [if_pos hαl, if_pos hI]
            split_ifs with h
            · rw [le_div_iff₀ (Real.exp_pos _)]; linarith
            · exact div_nonneg (T_nonneg ρ hρ0 hρ1 _ hfl0 y) (Real.exp_pos _).le
          calc ((2:ℝ) ^ n)⁻¹ * ∑ y, ind l y
              ≤ ((2:ℝ) ^ n)⁻¹ * ∑ y, T ρ (f l) y / Real.exp (r / 2) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => hpt2 y))
                  (inv_nonneg.2 hN2.le)
            _ = (((2:ℝ) ^ n)⁻¹ * ∑ x, f l x) / Real.exp (r / 2) := by
                rw [← Finset.sum_div, T_sum]; ring
            _ = 1 / Real.exp (r / 2) := by rw [hEf]
            _ = Real.exp (-(r / 2)) := by rw [one_div, ← Real.exp_neg]
            _ ≤ Real.exp (-(c' * r)) := Real.exp_le_exp.2 (by
                have := mul_le_mul_of_nonneg_right hc'1 hr0
                linarith)
        · have hfle : ∀ x, f l x ≤ Real.exp (Real.sqrt n) := by
            intro x
            push_neg at hI
            rw [hf, ← hr]
            dsimp only
            rw [inv_mul_le_iff₀ hαl]
            exact hI x
          have h := hc n (f l) hfl0 hEf hfle
          rw [← hρ, ← hr] at h
          calc ((2:ℝ) ^ n)⁻¹ * ∑ y, ind l y
              = ((2:ℝ) ^ n)⁻¹ * ∑ y, (if 7 / 2 ≤ T ρ (f l) y then (1:ℝ) else 0) := by
                congr 1
                refine Finset.sum_congr rfl (fun y _ => ?_)
                rw [hind]
                dsimp only
                rw [if_pos hαl, if_neg hI]
            _ ≤ Real.exp (-(c * r)) := h
            _ ≤ Real.exp (-(c' * r)) := Real.exp_le_exp.2 (by
                have := mul_le_mul_of_nonneg_right hc'2 hr0
                linarith)
      · have h0 : ∀ y, ind l y = 0 := by
          intro y; rw [hind]; dsimp only; rw [if_neg hαl]
        simp only [h0, Finset.sum_const_zero, mul_zero]
        exact (Real.exp_pos _).le
    have htot : (2:ℝ) ^ n ≤ ∑ l, ∑ y, ind l y := by
      calc (2:ℝ) ^ n = ∑ _y : Cube n, (1:ℝ) := card_sum.symm
        _ ≤ ∑ y, ∑ l, ind l y := Finset.sum_le_sum (fun y _ => hpt y)
        _ = ∑ l, ∑ y, ind l y := Finset.sum_comm
    have h1 : 1 ≤ (N:ℝ) * Real.exp (-(c' * r)) := by
      have hs := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hsum_ind l)
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hs
      have h2 : 1 ≤ ((2:ℝ) ^ n)⁻¹ * ∑ l, ∑ y, ind l y := by
        calc (1:ℝ) = ((2:ℝ) ^ n)⁻¹ * (2:ℝ) ^ n := (inv_mul_cancel₀ hN2.ne').symm
          _ ≤ ((2:ℝ) ^ n)⁻¹ * ∑ l, ∑ y, ind l y :=
              mul_le_mul_of_nonneg_left htot (inv_nonneg.2 hN2.le)
      linarith
    have h3 : (N:ℝ) * Real.exp (-(c' * r)) < 1 := by
      calc (N:ℝ) * Real.exp (-(c' * r)) < Real.exp (C * r) * Real.exp (-(c' * r)) :=
            mul_lt_mul_of_pos_right hlt (Real.exp_pos _)
        _ = Real.exp (C * r + -(c' * r)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by
            have := mul_le_mul_of_nonneg_right (show C ≤ c' by linarith) hr0
            linarith)
        _ = 1 := Real.exp_zero
    linarith

end Aux_L1G

end PSDPolyApprox

open ExtensionComplexity.TSP PSDPolyApprox in
theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ N : ℕ,
      HasNonnegFactorization (slackSubmatrix ε n) N → Real.exp (C * Real.sqrt n) ≤ N :=
  PSDPolyApprox.Aux_L1G.nfl ε hε0 hε1
