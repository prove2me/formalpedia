-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P12.reflectionDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:16:30.86952+00:00
-- url     : https://prove2.me/submissions/cb0c30b5-8d10-4c31-b71a-67535394d976

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12

noncomputable section
open scoped BigOperators Matrix

namespace X5RD
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def P (v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ := Matrix.of fun i j => v i * star (v j)

def ip (a b : EuclideanSpace ℂ ι) : ℂ := ∑ k, star (a k) * b k

lemma refl_eq (v : EuclideanSpace ℂ ι) : householderReflection v = 1 - 2 • P v := by
  ext i j
  simp [householderReflection, P, Matrix.one_apply, mul_assoc]

lemma P_mul (a b : EuclideanSpace ℂ ι) (h : ip a b = 0) : P a * P b = 0 := by
  ext i j
  simp only [P, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  have : ∑ k, a i * star (a k) * (b k * star (b j)) = a i * star (b j) * ip a b := by
    rw [ip, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this, h, mul_zero]

lemma list_prod (L : List (EuclideanSpace ℂ ι)) (hL : L.Pairwise (fun a b => ip a b = 0)) :
    (L.map householderReflection).prod = 1 - 2 • (L.map P).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    rw [List.map_cons, List.prod_cons, ih hL.2, List.map_cons, List.sum_cons, refl_eq]
    have h0 : P a * (L.map P).sum = 0 := by
      rw [← List.sum_map_mul_left]
      apply List.sum_eq_zero
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      exact P_mul a c (hL.1 c hc)
    have : (1 - 2 • P a) * (1 - 2 • (L.map P).sum) =
        1 - 2 • P a - 2 • (L.map P).sum + 4 • (P a * (L.map P).sum) := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm]
      norm_num; abel
    rw [this, h0, smul_add]; simp; abel

lemma ordered_prod {t : ℕ} (w : Fin t → EuclideanSpace ℂ ι)
    (hw : ∀ i j, i ≠ j → ip (w i) (w j) = 0) :
    orderedProd (fun j => householderReflection (w j)) = 1 - 2 • ∑ j, P (w j) := by
  unfold orderedProd
  have e : (List.ofFn fun j => householderReflection (w j)).reverse =
      (List.ofFn w).reverse.map householderReflection := by
    rw [List.map_reverse, List.map_ofFn]; rfl
  rw [e, list_prod]
  · rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]; rfl
  · rw [List.pairwise_reverse, List.pairwise_ofFn]
    intro i j hij
    exact hw j i (ne_of_gt hij)

end X5RD


noncomputable section
open scoped BigOperators Matrix

namespace X5RD
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12

variable {n : ℕ}

local notation "r2" => ((Real.sqrt 2 : ℝ) : ℂ)

lemma r2_ne : r2 ≠ 0 := by
  have : Real.sqrt 2 ≠ 0 := by positivity
  exact_mod_cast this

lemma r2_sq : r2 * r2 = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma star_r2inv : star (r2⁻¹) = r2⁻¹ := by
  rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _

lemma r2inv_sq : r2⁻¹ * r2⁻¹ = 1 / 2 := by
  rw [← mul_inv, r2_sq]; norm_num

lemma wv_apply (U : Matrix (Qubits n) (Qubits n) ℂ) (j : Qubits n) (s : Bool) (c : Bool)
    (x : Qubits n) :
    reflectionVector U j s (c, x) =
      r2⁻¹ * (if c then (if x = j then 1 else 0) else (if s then -1 else 1) * U x j) := by
  cases c <;> cases s <;>
    simp [reflectionVector, tensorVec, ket, EuclideanSpace.single_apply]

lemma w_ip (U : Matrix (Qubits n) (Qubits n) ℂ) (hU : star U * U = 1) (j k : Qubits n)
    (s : Bool) :
    ip (reflectionVector U j s) (reflectionVector U k s) = if j = k then 1 else 0 := by
  have hUU : ∑ x, star (U x j) * U x k = if j = k then 1 else 0 := by
    have := congrFun (congrFun hU j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [Matrix.star_apply] using this
  rw [ip, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [wv_apply, if_true, Bool.false_eq_true, if_false, star_mul', star_r2inv]
  have e1 : ∑ y : Qubits n, r2⁻¹ * star (if y = j then (1 : ℂ) else 0) *
      (r2⁻¹ * (if y = k then 1 else 0)) = (1 / 2) * (if j = k then 1 else 0) := by
    have : ∀ y : Qubits n, r2⁻¹ * star (if y = j then (1 : ℂ) else 0) *
        (r2⁻¹ * (if y = k then 1 else 0)) = if j = y then (1 / 2) * (if j = k then 1 else 0) else 0 := by
      intro y
      by_cases hy : j = y
      · subst hy; simp only [if_true]
        split_ifs <;> simp [r2inv_sq]
      · rw [if_neg hy, if_neg (Ne.symm hy)]; simp
    simp_rw [this]
    rw [Finset.sum_ite_eq]; simp
  have e2 : ∑ y : Qubits n, r2⁻¹ * (star (if s then (-1 : ℂ) else 1) * star (U y j)) *
      (r2⁻¹ * ((if s then -1 else 1) * U y k)) = (1 / 2) * (if j = k then 1 else 0) := by
    rw [← hUU, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hs : star (if s then (-1 : ℂ) else 1) * (if s then -1 else 1) = 1 := by
      cases s <;> simp
    rw [← r2inv_sq]
    linear_combination (r2⁻¹ * r2⁻¹ * star (U y j) * U y k) * hs
  rw [e1, e2]
  split_ifs <;> norm_num

end X5RD


noncomputable section
open scoped BigOperators Matrix

namespace X5RD
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12

variable {n : ℕ}

local notation "r2" => ((Real.sqrt 2 : ℝ) : ℂ)

lemma half_sum {κ : Type*} [Fintype κ] (a b : κ → ℂ) :
    ∑ j, (r2⁻¹ * a j) * star (r2⁻¹ * b j) = 1 / 2 * ∑ j, a j * star (b j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul', star_r2inv, ← r2inv_sq]; ring

lemma star_d (p : Prop) [Decidable p] :
    star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

lemma unit_of {κ : Type*} [Fintype κ] [DecidableEq κ] (Q : Matrix κ κ ℂ) (hQ : Q * Q = Q)
    (hs : star Q = Q) : (1 - 2 • Q) * star (1 - 2 • Q) = 1 := by
  rw [star_sub, star_one, star_nsmul, hs]
  have : (1 - 2 • Q) * (1 - 2 • Q) = 1 - 4 • Q + 4 • (Q * Q) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm]
    rw [show (2 : ℕ) * 2 = 4 by rfl]
    rw [show (4 : ℕ) • Q = 2 • Q + 2 • Q by rw [← add_smul]]
    abel
  rw [this, hQ]; abel

lemma Q_eq (U : Matrix (Qubits n) (Qubits n) ℂ) (hU : U * star U = 1) :
    1 - 2 • ∑ j, P (reflectionVector U j true) = simulationDilation U := by
  have hUU : ∀ x y, ∑ j, U x j * star (U y j) = if x = y then 1 else 0 := by
    intro x y
    have := congrFun (congrFun hU x) y
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [Matrix.star_apply] using this
  ext ⟨c, x⟩ ⟨d, y⟩
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, P, Matrix.of_apply, wv_apply,
    half_sum, simulationDilation, Matrix.one_apply, Prod.mk.injEq]
  cases c <;> cases d <;> simp only [if_true, Bool.false_eq_true, if_false, true_and, false_and]
  · simp only [neg_mul, one_mul, star_neg, mul_neg, neg_neg, hUU]
    split_ifs <;> norm_num
  · simp only [neg_mul, one_mul, star_d, mul_ite, mul_one, mul_zero,
      Finset.sum_neg_distrib, neg_neg, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  · simp only [neg_mul, one_mul, star_neg, mul_neg, ite_mul, one_mul, zero_mul,
      Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp
  · simp only [star_d, mul_ite, mul_one, mul_zero, ite_mul, one_mul,
      zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_eq']
    by_cases h : x = y
    · subst h; simp
    · simp [h]

lemma P_self (a : EuclideanSpace ℂ (Bool × Qubits n)) (h : ip a a = 1) : P a * P a = P a := by
  ext i j
  simp only [P, Matrix.mul_apply, Matrix.of_apply]
  have : ∑ k, a i * star (a k) * (a k * star (a j)) = a i * star (a j) * ip a a := by
    rw [ip, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this, h, mul_one]

lemma unitary_dil (U : Matrix (Qubits n) (Qubits n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    simulationDilation U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  set Q := ∑ j, P (reflectionVector U j true)
  have hQ : Q * Q = Q := by
    simp only [Q, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · exact P_self _ (by rw [w_ip U h2]; simp)
    · intro k _ hk
      exact P_mul _ _ (by rw [w_ip U h2]; simp [Ne.symm hk])
    · simp
  have hs : star Q = Q := by
    simp only [Q, star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext a b
    simp [P, Matrix.star_apply, mul_comm]
  rw [← Q_eq U h1, Matrix.mem_unitaryGroup_iff]
  exact unit_of Q hQ hs

end X5RD


noncomputable section
open scoped BigOperators Matrix

namespace X5RD
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12

variable {n : ℕ}

local notation "r2" => ((Real.sqrt 2 : ℝ) : ℂ)

lemma act_dil (U : Matrix (Qubits n) (Qubits n) ℂ) (psi : EuclideanSpace ℂ (Qubits n)) :
    act (simulationDilation U) (tensorVec (ket true) psi) = tensorVec (ket false) (act U psi) := by
  ext ⟨c, x⟩
  simp only [act, tensorVec, ket, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_bool, simulationDilation, Matrix.of_apply, PiLp.toLp_apply,
    EuclideanSpace.single_apply]
  cases c <;> simp

lemma state_w (U : Matrix (Qubits n) (Qubits n) ℂ) (hU : star U * U = 1) (j : Qubits n)
    (s : Bool) : IsState (reflectionVector U j s) := by
  have h := w_ip U hU j j s
  simp only [if_true] at h
  have hi : inner ℂ (reflectionVector U j s) (reflectionVector U j s) = 1 := by
    rw [← h, PiLp.inner_apply, ip]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.inner_apply, mul_comm]; rfl
  rw [inner_self_eq_norm_sq_to_K] at hi
  have h2 : ‖reflectionVector U j s‖ ^ 2 = 1 := Complex.ofReal_eq_one.1 (by push_cast; exact hi)
  unfold IsState
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)] at h2

lemma r2_pow (k : ℕ) : ∃ a b : ℤ, r2 ^ k = (a : ℂ) + (b : ℂ) * r2 := by
  induction k with
  | zero => exact ⟨1, 0, by simp⟩
  | succ k ih =>
    obtain ⟨a, b, h⟩ := ih
    refine ⟨2 * b, a, ?_⟩
    rw [pow_succ, h]
    have := r2_sq
    push_cast
    linear_combination (b : ℂ) * this

lemma denom (U : Matrix (Qubits n) (Qubits n) ℂ) (kappa : ℕ)
    (hU : ∀ i j, HasDenominator (Real.sqrt 2) kappa (U i j)) (j : Qubits n) (s : Bool)
    (z : Bool × Qubits n) :
    HasDenominator (Real.sqrt 2) (kappa + 1) (reflectionVector U j s z) := by
  obtain ⟨c, x⟩ := z
  rw [wv_apply]
  have hr := r2_ne
  have hk : r2 ^ kappa ≠ 0 := pow_ne_zero _ hr
  cases c
  · obtain ⟨a, b, c, d, h⟩ := hU x j
    simp only [Bool.false_eq_true, if_false]
    cases s
    · refine ⟨a, b, c, d, ?_⟩
      simp only [Bool.false_eq_true, if_false, one_mul, h, pow_succ]
      field_simp
    · refine ⟨-a, -b, -c, -d, ?_⟩
      simp only [if_true, h, pow_succ]
      push_cast
      field_simp
      ring
  · simp only [if_true]
    by_cases hx : x = j
    · obtain ⟨a, b, h⟩ := r2_pow kappa
      refine ⟨a, b, 0, 0, ?_⟩
      simp only [if_pos hx, Int.cast_zero, zero_mul, add_zero, mul_zero, pow_succ, ← h]
      field_simp
    · refine ⟨0, 0, 0, 0, ?_⟩
      simp [hx]

end X5RD


open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12 in
theorem solution (n : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    simulationDilation U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ ∧
    (∀ psi : EuclideanSpace ℂ (Qubits n), IsState psi →
      act (simulationDilation U) (tensorVec (ket true) psi) = tensorVec (ket false) (act U psi)) ∧
    (∀ (j : Qubits n) (s : Bool), IsState (reflectionVector U j s)) ∧
    simulationDilation U = orderedProd (fun j : Fin (2 ^ n) =>
      householderReflection (reflectionVector U ((bitsEquivFin n).symm j) true)) ∧
    (∀ kappa : ℕ, (∀ i j, HasDenominator (Real.sqrt 2) kappa (U i j)) →
      ∀ (j : Qubits n) (s : Bool) (z : Bool × Qubits n),
        HasDenominator (Real.sqrt 2) (kappa + 1) (reflectionVector U j s z)) := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  refine ⟨X5RD.unitary_dil U hU, fun psi _ => X5RD.act_dil U psi,
    fun j s => X5RD.state_w U h2 j s, ?_, fun kappa hk j s z => X5RD.denom U kappa hk j s z⟩
  rw [X5RD.ordered_prod, ← X5RD.Q_eq U h1]
  · congr 2
    exact (Equiv.sum_comp (bitsEquivFin n).symm (fun x => X5RD.P (reflectionVector U x true))).symm
  · intro i j hij
    rw [X5RD.w_ip U h2]
    simp [hij]
