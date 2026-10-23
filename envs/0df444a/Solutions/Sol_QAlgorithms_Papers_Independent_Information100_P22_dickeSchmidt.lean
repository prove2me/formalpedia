-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.dickeSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:04:25.147805+00:00
-- url     : https://prove2.me/submissions/0e85d770-3969-4dff-89db-8c0ada528dc3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

open scoped ComplexConjugate ComplexOrder Matrix
open Matrix Polynomial

noncomputable section

namespace X8P22E
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22

theorem x8_tr_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x8_tr_cfc_eq {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, x8_tr_aeval, x8_tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem x8_pow_mul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x8_tr_pow_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x8_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- tr f(V Vᴴ) = tr f((Vᴴ V)ᵀ) when f 0 = 0. -/
theorem x8_ent_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    QAlgorithms.vnEntropy (V * Vᴴ) = QAlgorithms.vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold QAlgorithms.vnEntropy
  rw [x8_tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x8_tr_pow_swap _ _ k hk]


theorem x8_pow {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℂ)
    (h : A = W * diagonal d * Wᴴ) (n : ℕ) : A ^ n = W * diagonal (d ^ n) * Wᴴ := by
  induction n with
  | zero => simp [hW2]
  | succ n ih =>
    rw [pow_succ, ih, h]
    have : W * diagonal (d ^ n) * Wᴴ * (W * diagonal d * Wᴴ) =
        W * (diagonal (d ^ n) * (Wᴴ * W) * diagonal d) * Wᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, hW1, Matrix.mul_one, diagonal_mul_diagonal, pow_succ]
    rfl

theorem x8_aeval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (p : ℝ[X]) :
    aeval A p = W * diagonal (fun k => ((p.eval (d k) : ℝ) : ℂ)) * Wᴴ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    congr 3; ext k; simp
  | monomial n c =>
    rw [aeval_monomial, x8_pow A W hW1 hW2 _ h n]
    simp only [eval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← diagonal_smul]
    congr 3; ext k; simp [Pi.pow_apply]

theorem x8_trace_cfc {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ k, ((f (d k) : ℝ) : ℂ) := by
  classical
  let S : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hA.eigenvalues
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A := by
    apply cfc_congr
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))).symm
  rw [h1, cfc_polynomial p A, x8_aeval A W hW1 hW2 d h p, Matrix.trace_mul_cycle, hW1,
    Matrix.one_mul, trace_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]



theorem x8_ent_diag {α : Type*} [Fintype α] [DecidableEq α] (q : α → ℝ) :
    vnEntropy (diagonal (fun i => (q i : ℂ))) = -∑ i, q i * Real.logb 2 (q i) := by
  unfold vnEntropy
  rw [x8_trace_cfc _ (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp [Pi.star_apply]))
    (1 : Matrix α α ℂ) (by simp) (by simp) q (by simp)]
  simp [Complex.re_sum]

theorem x8_cnt (T : Type) [Fintype T] [DecidableEq T] (s : ℕ) :
    (Finset.univ.filter (fun z : T → Bool => hammingWeight z = s)).card = (Fintype.card T).choose s := by
  rw [← Finset.card_univ, ← Finset.card_powersetCard]
  apply Finset.card_nbij' (fun z => Finset.univ.filter (fun t => z t = true)) (fun A t => decide (t ∈ A))
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hz⟩
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hA
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold hammingWeight
    rw [← hA.2]; congr 1; ext t; simp
  · intro z _; funext t; simp
  · intro A _; ext t; simp


end X8P22E
namespace X8P22E
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22

theorem x8_wle {ν : ℕ} (x : Fin ν → Bool) : hammingWeight x ≤ ν := by
  unfold hammingWeight
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem x8_dk (ν j : ℕ) (x : Fin ν → Bool) : (dicke (I := Fin ν) j).ofLp x =
    if hammingWeight x = j then (((Real.sqrt (ν.choose j : ℝ))⁻¹ : ℝ) : ℂ) else 0 := by
  simp [dicke]

theorem x8_dr (ν r : ℕ) (x y : Fin ν → Bool) : (dickeResource (Fin ν) r).ofLp (x, y) =
    if hammingWeight x + hammingWeight y = r then (((Real.sqrt ((2 * ν).choose r : ℝ))⁻¹ : ℝ) : ℂ) else 0 := by
  simp [dickeResource]

theorem x8_sq (c : ℕ) (hc : 0 < c) : (Real.sqrt (c : ℝ))⁻¹ * (Real.sqrt (c : ℝ))⁻¹ = (c : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by positivity)]

theorem x8_lam_pos (ν r j : ℕ) (hr : r ≤ 2 * ν) (hj : j ∈ Finset.Icc (r - ν) (min r ν)) :
    0 < dickeLambda ν r j := by
  simp only [Finset.mem_Icc] at hj
  unfold dickeLambda
  have h1 : 0 < ν.choose j := Nat.choose_pos (by omega)
  have h2 : 0 < ν.choose (r - j) := Nat.choose_pos (by omega)
  have h3 : 0 < (2 * ν).choose r := Nat.choose_pos hr
  positivity

theorem x8_coef (ν r j : ℕ) (hr : r ≤ 2 * ν) (hj : j ∈ Finset.Icc (r - ν) (min r ν)) :
    Real.sqrt (dickeLambda ν r j) * (Real.sqrt (ν.choose j : ℝ))⁻¹ * (Real.sqrt (ν.choose (r - j) : ℝ))⁻¹ =
      (Real.sqrt ((2 * ν).choose r : ℝ))⁻¹ := by
  simp only [Finset.mem_Icc] at hj
  have h1 : (0 : ℝ) < ν.choose j := by exact_mod_cast Nat.choose_pos (by omega)
  have h2 : (0 : ℝ) < ν.choose (r - j) := by exact_mod_cast Nat.choose_pos (by omega)
  have h3 : (0 : ℝ) < (2 * ν).choose r := by exact_mod_cast Nat.choose_pos hr
  unfold dickeLambda
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul h1.le]
  have := Real.sqrt_pos.mpr h1
  have := Real.sqrt_pos.mpr h2
  have := Real.sqrt_pos.mpr h3
  field_simp

theorem x8_vec (ν r : ℕ) (hr : r ≤ 2 * ν) :
    dickeResource (Fin ν) r =
      ∑ j ∈ Finset.Icc (r-ν) (min r ν), (Real.sqrt (dickeLambda ν r j) : ℂ) •
        tensorVec (dicke (I := Fin ν) j) (dicke (I := Fin ν) (r-j)) := by
  ext ⟨x, y⟩
  rw [x8_dr, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.smul_apply, tensorVec, x8_dk, smul_eq_mul]
  have hx := x8_wle x
  have hy := x8_wle y
  by_cases h : hammingWeight x + hammingWeight y = r
  · rw [if_pos h]
    have hmem : hammingWeight x ∈ Finset.Icc (r - ν) (min r ν) := by
      simp only [Finset.mem_Icc]; omega
    rw [Finset.sum_eq_single (hammingWeight x)]
    · rw [if_pos rfl, if_pos (by omega), ← x8_coef ν r _ hr hmem]
      push_cast; ring
    · intro j _ hj; rw [if_neg (Ne.symm hj)]; simp
    · intro h'; exact absurd hmem h'
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    by_cases h1 : hammingWeight x = j
    · rw [if_pos h1, if_neg (by omega)]; simp
    · rw [if_neg h1]; simp

theorem x8_state (ν j : ℕ) (hj : j ≤ ν) : IsState (dicke (I := Fin ν) j) := by
  rw [IsState, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  have : ∀ x : Fin ν → Bool, ‖(dicke (I := Fin ν) j).ofLp x‖ ^ 2 =
      if hammingWeight x = j then ((ν.choose j : ℝ))⁻¹ else 0 := by
    intro x
    rw [x8_dk]
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, x8_sq _ (Nat.choose_pos hj)]
    · simp
  simp only [this]
  rw [← Finset.sum_filter, Finset.sum_const, x8_cnt, Fintype.card_fin, nsmul_eq_mul]
  have : (0 : ℝ) < ν.choose j := by exact_mod_cast Nat.choose_pos hj
  field_simp

theorem x8_inner0 (ν j l : ℕ) (h : j ≠ l) : inner ℂ (dicke (I := Fin ν) j) (dicke (I := Fin ν) l) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro x _
  simp only [x8_dk]
  by_cases h1 : hammingWeight x = j
  · rw [if_neg (show ¬ hammingWeight x = l by omega)]; simp
  · rw [if_neg h1]; simp

abbrev KK (ν r : ℕ) := Finset.Icc (r - ν) (min r ν)

def Nm (ν r : ℕ) : Matrix (Fin ν → Bool) (KK ν r) ℂ :=
  fun x j => (Real.sqrt (dickeLambda ν r j) : ℂ) * (dicke (I := Fin ν) j.1).ofLp x

theorem x8_orth (ν j l : ℕ) (hj : j ≤ ν) :
    ∑ x : Fin ν → Bool, conj ((dicke (I := Fin ν) j).ofLp x) * (dicke (I := Fin ν) l).ofLp x =
      if j = l then 1 else 0 := by
  have hs : ∀ x : Fin ν → Bool, conj ((dicke (I := Fin ν) j).ofLp x) * (dicke (I := Fin ν) l).ofLp x =
      if hammingWeight x = j ∧ j = l then (((ν.choose j : ℝ))⁻¹ : ℂ) else 0 := by
    intro x
    simp only [x8_dk]
    by_cases h1 : hammingWeight x = j
    · by_cases h2 : j = l
      · subst h2
        rw [if_pos h1, if_pos ⟨h1, rfl⟩, Complex.conj_ofReal, ← Complex.ofReal_mul,
          x8_sq _ (Nat.choose_pos hj)]
        push_cast; rfl
      · have h3 : ¬ hammingWeight x = l := by omega
        simp [h1, h2, h3]
    · simp [h1]
  simp only [hs]
  by_cases h2 : j = l
  · simp only [h2, and_true, if_true]
    rw [← Finset.sum_filter, Finset.sum_const, x8_cnt, Fintype.card_fin, nsmul_eq_mul]
    subst h2
    have : (ν.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    push_cast
    field_simp
  · simp [h2]

theorem x8_NN (ν r : ℕ) (hr : r ≤ 2 * ν) :
    (Nm ν r)ᴴ * Nm ν r = diagonal (fun j : KK ν r => ((dickeLambda ν r j : ℝ) : ℂ)) := by
  ext j l
  simp only [mul_apply, conjTranspose_apply, Nm, star_mul', diagonal_apply]
  have hj := j.2
  simp only [KK, Finset.mem_Icc] at hj
  have : ∀ x : Fin ν → Bool, star ((Real.sqrt (dickeLambda ν r j) : ℂ)) * star ((dicke (I := Fin ν) j.1).ofLp x) *
      ((Real.sqrt (dickeLambda ν r l) : ℂ) * (dicke (I := Fin ν) l.1).ofLp x) =
      ((Real.sqrt (dickeLambda ν r j) * Real.sqrt (dickeLambda ν r l) : ℝ) : ℂ) *
        (conj ((dicke (I := Fin ν) j.1).ofLp x) * (dicke (I := Fin ν) l.1).ofLp x) := by
    intro x
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  simp only [this]
  rw [← Finset.mul_sum, x8_orth ν j.1 l.1 (by omega)]
  by_cases h : j = l
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_one, Real.mul_self_sqrt (x8_lam_pos ν r j hr j.2).le]
  · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h, mul_zero]

theorem x8_rho (ν r : ℕ) (hr : r ≤ 2 * ν) :
    traceRight (pureDensity (dickeResource (Fin ν) r)) = Nm ν r * (Nm ν r)ᴴ := by
  ext x x'
  have hC2 : 0 < (2 * ν).choose r := Nat.choose_pos hr
  have hx := x8_wle x
  have hx' := x8_wle x'
  -- closed form of both sides
  have hL : traceRight (pureDensity (dickeResource (Fin ν) r)) x x' =
      if hammingWeight x = hammingWeight x' ∧ hammingWeight x ∈ KK ν r then
        (((ν.choose (r - hammingWeight x) : ℝ) * ((2 * ν).choose r : ℝ)⁻¹ : ℝ) : ℂ) else 0 := by
    simp only [traceRight, pureDensity, of_apply, x8_dr]
    have hs : ∀ y : Fin ν → Bool,
        ((if hammingWeight x + hammingWeight y = r then (((Real.sqrt ((2 * ν).choose r : ℝ))⁻¹ : ℝ) : ℂ) else 0) *
          conj (if hammingWeight x' + hammingWeight y = r then (((Real.sqrt ((2 * ν).choose r : ℝ))⁻¹ : ℝ) : ℂ) else 0)) =
        if (hammingWeight x = hammingWeight x' ∧ hammingWeight x ∈ KK ν r) ∧ hammingWeight y = r - hammingWeight x
          then ((((2 * ν).choose r : ℝ)⁻¹ : ℝ) : ℂ) else 0 := by
      intro y
      have hy := x8_wle y
      by_cases h1 : hammingWeight x + hammingWeight y = r
      · by_cases h2 : hammingWeight x' + hammingWeight y = r
        · rw [if_pos h1, if_pos h2, if_pos (by simp only [KK, Finset.mem_Icc]; omega), Complex.conj_ofReal,
            ← Complex.ofReal_mul, x8_sq _ hC2]
        · rw [if_pos h1, if_neg h2, if_neg (by simp only [KK, Finset.mem_Icc]; omega)]; simp
      · rw [if_neg h1, zero_mul, if_neg (by simp only [KK, Finset.mem_Icc]; omega)]
    simp only [hs]
    by_cases hQ : hammingWeight x = hammingWeight x' ∧ hammingWeight x ∈ KK ν r
    · rw [if_pos hQ, ← Finset.sum_filter]
      have : Finset.univ.filter (fun y : Fin ν → Bool => (hammingWeight x = hammingWeight x' ∧
          hammingWeight x ∈ KK ν r) ∧ hammingWeight y = r - hammingWeight x) =
          Finset.univ.filter (fun y : Fin ν → Bool => hammingWeight y = r - hammingWeight x) := by
        ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨hQ, h⟩⟩
      rw [this, Finset.sum_const, x8_cnt, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    · rw [if_neg hQ]; apply Finset.sum_eq_zero; intro y _; rw [if_neg (fun h => hQ h.1)]
  have hR : (Nm ν r * (Nm ν r)ᴴ) x x' =
      if hammingWeight x = hammingWeight x' ∧ hammingWeight x ∈ KK ν r then
        (((ν.choose (r - hammingWeight x) : ℝ) * ((2 * ν).choose r : ℝ)⁻¹ : ℝ) : ℂ) else 0 := by
    simp only [mul_apply, conjTranspose_apply, Nm, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [Finset.sum_coe_sort (KK ν r) (fun j => (Real.sqrt (dickeLambda ν r j) : ℂ) * (dicke (I := Fin ν) j).ofLp x *
      ((Real.sqrt (dickeLambda ν r j) : ℂ) * conj ((dicke (I := Fin ν) j).ofLp x')))]
    by_cases hQ : hammingWeight x = hammingWeight x' ∧ hammingWeight x ∈ KK ν r
    · rw [if_pos hQ, Finset.sum_eq_single (hammingWeight x)]
      · have hm := hQ.2
        simp only [KK, Finset.mem_Icc] at hm
        simp only [x8_dk, if_pos hQ.1.symm, Complex.conj_ofReal, if_true]
        have hc : (0 : ℝ) < ν.choose (hammingWeight x) := by exact_mod_cast Nat.choose_pos hx
        rw [show ((Real.sqrt (dickeLambda ν r (hammingWeight x)) : ℂ) * (((Real.sqrt (ν.choose (hammingWeight x) : ℝ))⁻¹ : ℝ) : ℂ) *
            ((Real.sqrt (dickeLambda ν r (hammingWeight x)) : ℂ) * (((Real.sqrt (ν.choose (hammingWeight x) : ℝ))⁻¹ : ℝ) : ℂ))) =
            (((Real.sqrt (dickeLambda ν r (hammingWeight x)) * Real.sqrt (dickeLambda ν r (hammingWeight x))) *
              ((Real.sqrt (ν.choose (hammingWeight x) : ℝ))⁻¹ * (Real.sqrt (ν.choose (hammingWeight x) : ℝ))⁻¹) : ℝ) : ℂ) by
            push_cast; ring]
        rw [Real.mul_self_sqrt (x8_lam_pos ν r _ hr hQ.2).le, x8_sq _ (Nat.choose_pos hx)]
        congr 1
        unfold dickeLambda
        field_simp
      · intro j _ hj
        simp only [x8_dk, if_neg (Ne.symm hj)]; simp
      · intro h; exact absurd hQ.2 h
    · rw [if_neg hQ]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [x8_dk]
      by_cases h1 : hammingWeight x = j
      · by_cases h2 : hammingWeight x' = j
        · exact absurd ⟨h1.trans h2.symm, h1 ▸ hj⟩ hQ
        · rw [if_neg h2]; simp
      · rw [if_neg h1]; simp
  rw [hL, hR]

theorem x8_cardK (ν r : ℕ) (hr : r ≤ 2 * ν) : (KK ν r).card = min r ν - (r - ν) + 1 := by
  rw [KK, Nat.card_Icc]; omega

theorem x8_rank (ν r : ℕ) (hr : r ≤ 2 * ν) :
    (traceRight (pureDensity (dickeResource (Fin ν) r))).rank = min r ν - (r - ν) + 1 := by
  rw [x8_rho ν r hr, Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self,
    x8_NN ν r hr, Matrix.rank_diagonal]
  have hall : ∀ j : KK ν r, ((dickeLambda ν r j : ℝ) : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (x8_lam_pos ν r j hr j.2).ne'
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hall), Fintype.card_coe, x8_cardK ν r hr]

theorem x8_entropy (ν r : ℕ) (hr : r ≤ 2 * ν) :
    vnEntropy (traceRight (pureDensity (dickeResource (Fin ν) r))) = dickeEntropy ν r := by
  rw [x8_rho ν r hr, x8_ent_swap, x8_NN ν r hr, diagonal_transpose, x8_ent_diag, dickeEntropy]
  congr 1
  exact Finset.sum_coe_sort (KK ν r) (fun j => dickeLambda ν r j * Real.logb 2 (dickeLambda ν r j))

theorem x8_vdm (ν r : ℕ) :
    ∑ j ∈ KK ν r, ν.choose j * ν.choose (r - j) = (2 * ν).choose r := by
  rw [two_mul, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_subset
  · intro j hj
    simp only [KK, Finset.mem_Icc] at hj
    simp only [Finset.mem_range]; omega
  · intro j hj hj'
    simp only [Finset.mem_range] at hj
    simp only [KK, Finset.mem_Icc, not_and_or, not_le] at hj'
    rcases hj' with h | h
    · rw [Nat.choose_eq_zero_of_lt (show ν < r - j by omega), mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (show ν < j by omega), zero_mul]

theorem x8_lam_sum (ν r : ℕ) (hr : r ≤ 2 * ν) : ∑ j ∈ KK ν r, dickeLambda ν r j = 1 := by
  unfold dickeLambda
  rw [← Finset.sum_div]
  have h3 : (0 : ℝ) < (2 * ν).choose r := by exact_mod_cast Nat.choose_pos hr
  rw [div_eq_one_iff_eq h3.ne']
  exact_mod_cast x8_vdm ν r

theorem x8_ent_le (ν r : ℕ) (hr : r ≤ 2 * ν) : dickeEntropy ν r ≤ Real.logb 2 (ν + 1) := by
  have hpos := fun j hj => x8_lam_pos ν r j hr hj
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := KK ν r) (w := fun j => dickeLambda ν r j)
    (p := fun j => (dickeLambda ν r j)⁻¹) (fun j hj => (hpos j hj).le) (x8_lam_sum ν r hr)
    (fun j hj => Set.mem_Ioi.mpr (inv_pos.mpr (hpos j hj)))
  simp only [smul_eq_mul] at hJ
  rw [Finset.sum_congr rfl (fun j hj => mul_inv_cancel₀ (hpos j hj).ne'), Finset.sum_const, nsmul_eq_mul,
    mul_one, x8_cardK ν r hr] at hJ
  have hE : dickeEntropy ν r = (∑ j ∈ KK ν r, dickeLambda ν r j * Real.log (dickeLambda ν r j)⁻¹) / Real.log 2 := by
    unfold dickeEntropy
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.logb, Real.log_inv]; ring
  rw [hE, Real.logb, div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)]
  refine hJ.trans (Real.log_le_log (by positivity) ?_)
  have : min r ν - (r - ν) + 1 ≤ ν + 1 := by omega
  exact_mod_cast this

theorem x8_main (nu r : ℕ) (hnu : 1 ≤ nu) (hr : r ≤ 2*nu) :
    dickeResource (Fin nu) r =
      ∑ j ∈ Finset.Icc (r-nu) (min r nu), (Real.sqrt (dickeLambda nu r j) : ℂ) •
        tensorVec (dicke (I := Fin nu) j) (dicke (I := Fin nu) (r-j)) ∧
    (∀ j ∈ Finset.Icc (r-nu) (min r nu), IsState (dicke (I := Fin nu) j) ∧
      IsState (dicke (I := Fin nu) (r-j))) ∧
    (∀ j ∈ Finset.Icc (r-nu) (min r nu), ∀ l ∈ Finset.Icc (r-nu) (min r nu), j ≠ l →
      inner ℂ (dicke (I := Fin nu) j) (dicke (I := Fin nu) l) = 0 ∧
      inner ℂ (dicke (I := Fin nu) (r-j)) (dicke (I := Fin nu) (r-l)) = 0) ∧
    (traceRight (pureDensity (dickeResource (Fin nu) r))).rank = min r nu-(r-nu)+1 ∧
    (traceRight (pureDensity (dickeResource (Fin nu) r))).rank ≤ nu+1 ∧
    vnEntropy (traceRight (pureDensity (dickeResource (Fin nu) r))) = dickeEntropy nu r ∧
    dickeEntropy nu r ≤ Real.logb 2 (nu+1) := by
  refine ⟨x8_vec nu r hr, fun j hj => ?_, fun j hj l hl hjl => ?_, x8_rank nu r hr, ?_,
    x8_entropy nu r hr, x8_ent_le nu r hr⟩
  · simp only [Finset.mem_Icc] at hj
    exact ⟨x8_state nu j (by omega), x8_state nu (r - j) (by omega)⟩
  · simp only [Finset.mem_Icc] at hj hl
    exact ⟨x8_inner0 nu j l hjl, x8_inner0 nu (r - j) (r - l) (by omega)⟩
  · rw [x8_rank nu r hr]; omega

end X8P22E

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22


open scoped ComplexConjugate ComplexOrder Matrix


local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

open QAlgorithms.Papers.Independent.Information100.P22 in
/-- Eqs.(S67)–(S68), PDF pp.42–43. Feasible interval protects the natural subtraction r-j. -/
theorem solution (nu r : ℕ) (hnu : 1 ≤ nu) (hr : r ≤ 2*nu) :
    dickeResource (Fin nu) r =
      ∑ j ∈ Finset.Icc (r-nu) (min r nu), (Real.sqrt (dickeLambda nu r j) : ℂ) •
        tensorVec (dicke (I := Fin nu) j) (dicke (I := Fin nu) (r-j)) ∧
    (∀ j ∈ Finset.Icc (r-nu) (min r nu), IsState (dicke (I := Fin nu) j) ∧
      IsState (dicke (I := Fin nu) (r-j))) ∧
    (∀ j ∈ Finset.Icc (r-nu) (min r nu), ∀ l ∈ Finset.Icc (r-nu) (min r nu), j ≠ l →
      inner ℂ (dicke (I := Fin nu) j) (dicke (I := Fin nu) l) = 0 ∧
      inner ℂ (dicke (I := Fin nu) (r-j)) (dicke (I := Fin nu) (r-l)) = 0) ∧
    (traceRight (pureDensity (dickeResource (Fin nu) r))).rank = min r nu-(r-nu)+1 ∧
    (traceRight (pureDensity (dickeResource (Fin nu) r))).rank ≤ nu+1 ∧
    vnEntropy (traceRight (pureDensity (dickeResource (Fin nu) r))) = dickeEntropy nu r ∧
    dickeEntropy nu r ≤ Real.logb 2 (nu+1) :=
  X8P22E.x8_main nu r hnu hr



