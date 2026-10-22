-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P17.positive_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:28:54.721146+00:00
-- url     : https://prove2.me/submissions/3bf2a469-1eda-4d3b-afcb-ed9d94716017

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17
open QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

theorem g74c_L1 {A : Type*} [Ring A] (x : A) (l : List A) (h : ∀ y ∈ l, x * y = -(y * x)) :
    x * l.prod = (-1 : A) ^ l.length * (l.prod * x) := by
  induction l with
  | nil => simp
  | cons y r ih =>
    simp only [List.prod_cons, List.length_cons]
    have hy := h y (by simp)
    have hr := ih (fun z hz => h z (by simp [hz]))
    rw [← mul_assoc, hy, neg_mul, mul_assoc, hr, pow_succ, ← mul_assoc y,
      ← ((Commute.neg_one_left y).pow_left r.length).eq]
    simp only [mul_assoc, neg_mul, mul_neg, mul_one, one_mul]

theorem g74c_L2 {A : Type*} [Ring A] : ∀ (n : ℕ) (f : Fin n → A),
    (∀ i j, i ≠ j → f i * f j = -(f j * f i)) →
    ∀ j, (List.ofFn f).prod * f j = (-1 : A) ^ (n - 1) * (f j * (List.ofFn f).prod)
  | 0, _, _, j => j.elim0
  | k + 1, f, hf, j => by
    rw [List.ofFn_succ, List.prod_cons]
    have h1 : f 0 * (List.ofFn fun i => f i.succ).prod =
        (-1 : A) ^ k * ((List.ofFn fun i => f i.succ).prod * f 0) := by
      have := g74c_L1 (f 0) (List.ofFn fun i => f i.succ) (by
        intro y hy
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hf _ _ (Fin.succ_ne_zero i).symm)
      simpa using this
    have hc : ∀ (m : ℕ) (z : A), (-1 : A) ^ m * z = z * (-1 : A) ^ m := fun m z =>
      ((Commute.neg_one_left z).pow_left m).eq
    refine Fin.cases ?_ (fun j' => ?_) j
    · have h2 : (List.ofFn fun i => f i.succ).prod * f 0 =
          (-1 : A) ^ k * (f 0 * (List.ofFn fun i => f i.succ).prod) := by
        rw [h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
      simp only [Nat.add_sub_cancel]
      rw [mul_assoc, h2, ← mul_assoc, ← hc, mul_assoc]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := j'.pos; omega⟩
      have ih := g74c_L2 (k' + 1) (fun i => f i.succ) (fun i j hij => hf _ _ (by simpa using hij)) j'
      simp only [Nat.add_sub_cancel] at ih ⊢
      rw [mul_assoc, ih, ← mul_assoc, ← hc, mul_assoc, ← mul_assoc (f 0), hf 0 j'.succ
        (Fin.succ_ne_zero j').symm, pow_succ]
      simp only [mul_assoc, neg_mul, mul_neg, mul_one, neg_inj, Fin.cases_succ]

def g74c_T : ℕ → ℕ
  | 0 => 0
  | n + 1 => g74c_T n + n

theorem g74c_L3 {A : Type*} [Ring A] [Algebra ℝ A] : ∀ (n : ℕ) (f : Fin n → A) (c : Fin n → ℝ),
    (∀ i j, i ≠ j → f i * f j = -(f j * f i)) → (∀ i, f i * f i = algebraMap ℝ A (c i)) →
    (List.ofFn f).prod * (List.ofFn f).prod = algebraMap ℝ A ((-1) ^ g74c_T n * ∏ i, c i)
  | 0, _, _, _, _ => by simp [g74c_T]
  | k + 1, f, c, hf, hc => by
    rw [List.ofFn_succ, List.prod_cons]
    have h1 : f 0 * (List.ofFn fun i => f i.succ).prod =
        (-1 : A) ^ k * ((List.ofFn fun i => f i.succ).prod * f 0) := by
      have := g74c_L1 (f 0) (List.ofFn fun i => f i.succ) (by
        intro y hy
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hf _ _ (Fin.succ_ne_zero i).symm)
      simpa using this
    have h2 : (List.ofFn fun i => f i.succ).prod * f 0 =
        (-1 : A) ^ k * (f 0 * (List.ofFn fun i => f i.succ).prod) := by
      rw [h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    have ih := g74c_L3 k (fun i => f i.succ) (fun i => c i.succ)
      (fun i j hij => hf _ _ (by simpa using hij)) (fun i => hc _)
    have hm : (-1 : A) ^ k = algebraMap ℝ A ((-1) ^ k) := by simp
    rw [mul_assoc, ← mul_assoc _ (f 0), h2, hm]
    simp only [mul_assoc]
    rw [← mul_assoc (f 0), ← Algebra.commutes]
    simp only [mul_assoc]
    rw [← mul_assoc (f 0) (f 0), hc, ih,
      ← map_mul, ← map_mul, Fin.prod_univ_succ, g74c_T, pow_add]
    congr 1; ring

theorem g74c_T4 (n : ℕ) : g74c_T (n + 4) = g74c_T n + (4 * n + 6) := by
  simp only [g74c_T]; ring

theorem g74c_Tpar : ∀ n : ℕ, (-1 : ℝ) ^ g74c_T n = if n % 4 = 0 ∨ n % 4 = 1 then 1 else -1
  | 0 => by simp [g74c_T]
  | 1 => by simp [g74c_T]
  | 2 => by norm_num [g74c_T]
  | 3 => by norm_num [g74c_T]
  | n + 4 => by
    rw [g74c_T4, pow_add, g74c_Tpar n, show 4 * n + 6 = 2 * (2 * n + 3) by ring, pow_mul]
    simp [Nat.add_mod_right]

theorem g74c_T2 : ∀ m : ℕ, Even (g74c_T (m + m) + m)
  | 0 => by simp [g74c_T]
  | m + 1 => by
    have := g74c_T2 m
    rw [show m + 1 + (m + 1) = (m + m) + 1 + 1 by ring]
    simp only [g74c_T]
    obtain ⟨r, hr⟩ := this
    exact ⟨r + 2 * m + 1, by omega⟩

theorem g74c_Q {d : ℕ} (g : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cliffordQ g x = -(g.toBilin' x x) := by
  unfold cliffordQ Matrix.toQuadraticForm'
  simp [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply', Matrix.toLinearMap₂'_apply']

theorem g74c_polarR {d : ℕ} (g : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    QuadraticMap.polar (cliffordQ g) x y = -(g.toBilin' x y + g.toBilin' y x) := by
  unfold cliffordQ Matrix.toQuadraticForm'
  rw [LinearMap.BilinMap.polar_toQuadraticMap]
  simp [Matrix.toBilin'_apply', Matrix.toLinearMap₂'_apply']
  ring

theorem g74c_anti (p q : ℕ) (e : Module.Basis (Fin (p + q)) ℝ (Fin (p + q) → ℝ))
    (he : PseudoOrthonormal p q e) (i j : Fin (p + q)) (hij : i ≠ j) :
    CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e i) *
      CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e j) =
    -(CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e j) *
      CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e i)) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := cliffordQ (signatureMatrix p q)) (e i) (e j)
  rw [g74c_polarR, he, he] at h
  simp only [signatureMatrix, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij.symm,
    add_zero, neg_zero, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem g74c_vol_comm (p q : ℕ) (e : Module.Basis (Fin (p + q)) ℝ (Fin (p + q) → ℝ))
    (he : PseudoOrthonormal p q e) (x : Fin (p + q) → ℝ) :
    volumeElement p q e * CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) x =
      (-1 : RealCl p q) ^ (p + q - 1) *
        (CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) x * volumeElement p q e) := by
  conv_lhs => rw [← e.sum_repr x]
  conv_rhs => rw [← e.sum_repr x]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact g74c_L2 _ _ (g74c_anti p q e he) j

theorem g74c_vol_sq (p q : ℕ) (e : Module.Basis (Fin (p + q)) ℝ (Fin (p + q) → ℝ))
    (he : PseudoOrthonormal p q e) :
    volumeElement p q e ^ 2 = algebraMap ℝ (RealCl p q)
      ((-1) ^ g74c_T (p + q) * ∏ i : Fin (p + q), -(signatureMatrix p q i i)) := by
  rw [sq]
  refine g74c_L3 _ _ _ (g74c_anti p q e he) (fun i => ?_)
  rw [CliffordAlgebra.ι_sq_scalar, g74c_Q, he]

/-- Lemma 4.2, PDF p. 26: positive-signature volume, both commutation and square formulas. -/
theorem solution (m : ℕ)
    (e : Module.Basis (Fin (m + 0)) ℝ ((Fin (m + 0) → ℝ))) (he : PseudoOrthonormal m 0 e) :
    (∀ x : (Fin (m + 0) → ℝ),
      if Even m then volumeElement m 0 e * CliffordAlgebra.ι (cliffordQ (signatureMatrix m 0)) x +
        CliffordAlgebra.ι (cliffordQ (signatureMatrix m 0)) x * volumeElement m 0 e = 0
      else volumeElement m 0 e * CliffordAlgebra.ι (cliffordQ (signatureMatrix m 0)) x =
        CliffordAlgebra.ι (cliffordQ (signatureMatrix m 0)) x * volumeElement m 0 e) ∧
    volumeElement m 0 e ^ 2 = if m % 4 = 0 ∨ m % 4 = 3 then 1 else -1 := by
  constructor
  · intro x
    rw [g74c_vol_comm m 0 e he x]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : x = 0 := funext fun i => Fin.elim0 i
      subst this; simp
    · split_ifs with hev
      · have : (-1 : RealCl m 0) ^ (m + 0 - 1) = -1 :=
          Odd.neg_one_pow (by obtain ⟨r, hr⟩ := hev; exact ⟨r - 1, by omega⟩)
        rw [this]; simp
      · have : (-1 : RealCl m 0) ^ (m + 0 - 1) = 1 :=
          Even.neg_one_pow (by
            obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hev; exact ⟨r, by omega⟩)
        rw [this]; simp
  · rw [g74c_vol_sq m 0 e he]
    have hp : ∏ i : Fin (m + 0), -(signatureMatrix m 0 i i) = (-1) ^ m := by
      rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℝ)) (fun i _ => by
        simp [signatureMatrix, i.isLt])]
      simp
    have hr : (-1 : ℝ) ^ g74c_T (m + 0) * ∏ i : Fin (m + 0), -(signatureMatrix m 0 i i) =
        if m % 4 = 0 ∨ m % 4 = 3 then 1 else -1 := by
      rw [hp, ← pow_add, show g74c_T (m + 0) + m = g74c_T (m + 1) from rfl, g74c_Tpar]
      simp only [show ((m + 1) % 4 = 0 ∨ (m + 1) % 4 = 1) ↔ (m % 4 = 0 ∨ m % 4 = 3) by omega]
    rw [hr]; split_ifs <;> simp
