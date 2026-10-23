-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.varianceTypical
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:55:52.951988+00:00
-- url     : https://prove2.me/submissions/26766cbe-a0e9-4a3d-8dd4-8428e7d1318d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Dependency50.P19 (count)

namespace X6TWL

section prob

variable {I : Type} [Fintype I] [DecidableEq I]

lemma exp_one {n : ℕ} (q : Fin n → I → ℝ) (hq : ∀ i, ∑ j, q i j = 1) (k : Fin n) (a : I → ℝ) :
    ∑ w : Fin n → I, (∏ m, q m (w m)) * a (w k) = ∑ j, q k j * a j := by
  have h := (Fintype.prod_sum (fun (m : Fin n) (j : I) => q m j * (if m = k then a j else 1))).symm
  have e1 : ∀ w : Fin n → I, ∏ m, q m (w m) * (if m = k then a (w m) else 1) =
      (∏ m, q m (w m)) * a (w k) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k (fun m => a (w m))]
    simp
  simp only [e1] at h
  rw [h]
  have e2 : ∀ m, ∑ j, q m j * (if m = k then a j else 1) =
      if m = k then ∑ j, q k j * a j else 1 := by
    intro m; split_ifs with hm
    · subst hm; simp
    · simp [hq]
  simp only [e2]
  rw [Finset.prod_ite_eq' Finset.univ k (fun _ => ∑ j, q k j * a j)]
  simp

lemma exp_two {n : ℕ} (q : Fin n → I → ℝ) (hq : ∀ i, ∑ j, q i j = 1) (k l : Fin n) (hkl : k ≠ l)
    (a b : I → ℝ) :
    ∑ w : Fin n → I, (∏ m, q m (w m)) * (a (w k) * b (w l)) =
      (∑ j, q k j * a j) * ∑ j, q l j * b j := by
  have h := (Fintype.prod_sum (fun (m : Fin n) (j : I) =>
    q m j * ((if m = k then a j else 1) * (if m = l then b j else 1)))).symm
  have e1 : ∀ w : Fin n → I, ∏ m, q m (w m) * ((if m = k then a (w m) else 1) *
      (if m = l then b (w m) else 1)) = (∏ m, q m (w m)) * (a (w k) * b (w l)) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ k (fun m => a (w m)),
      Finset.prod_ite_eq' Finset.univ l (fun m => b (w m))]
    simp
  simp only [e1] at h
  rw [h]
  have e2 : ∀ m, ∑ j, q m j * ((if m = k then a j else 1) * (if m = l then b j else 1)) =
      (if m = k then ∑ j, q k j * a j else 1) * (if m = l then ∑ j, q l j * b j else 1) := by
    intro m
    by_cases h1 : m = k
    · subst h1; simp [hkl]
    · by_cases h2 : m = l
      · subst h2; simp [h1]
      · simp [h1, h2, hq]
  simp only [e2]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k (fun _ => ∑ j, q k j * a j),
    Finset.prod_ite_eq' Finset.univ l (fun _ => ∑ j, q l j * b j)]
  simp

lemma count_eq {n : ℕ} (w : Fin n → I) (i : I) :
    (count w i : ℝ) = ∑ k, (if w k = i then (1 : ℝ) else 0) := by
  unfold count
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma variance {n : ℕ} (q : Fin n → I → ℝ) (hq : ∀ i, ∑ j, q i j = 1) (i : I) :
    ∑ w : Fin n → I, (∏ m, q m (w m)) * ((count w i : ℝ) - ∑ k, q k i) ^ 2 =
      ∑ k, q k i * (1 - q k i) := by
  set g : Fin n → I → ℝ := fun k j => (if j = i then 1 else 0) - q k i
  have hg : ∀ w : Fin n → I, (count w i : ℝ) - ∑ k, q k i = ∑ k, g k (w k) := by
    intro w
    rw [count_eq]; simp only [g, Finset.sum_sub_distrib]
  have hg0 : ∀ k, ∑ j, q k j * g k j = 0 := by
    intro k
    simp only [g, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hq, one_mul, sub_self]
  have hg2 : ∀ k, ∑ j, q k j * (g k j * g k j) = q k i * (1 - q k i) := by
    intro k
    have : ∀ j, q k j * (g k j * g k j) =
        (if j = i then q k i * ((1 - q k i) ^ 2 - q k i ^ 2) else 0) + q k j * q k i ^ 2 := by
      intro j; simp only [g]; split_ifs with h
      · subst h; ring
      · ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.sum_mul, hq]
    ring
  have key : ∀ k : Fin n, ∑ l : Fin n, ∑ w : Fin n → I, (∏ m, q m (w m)) *
      (g k (w k) * g l (w l)) = q k i * (1 - q k i) := by
    intro k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have h1 : ∑ w : Fin n → I, (∏ m, q m (w m)) * (g k (w k) * g k (w k)) =
        q k i * (1 - q k i) := by
      rw [← hg2 k]
      exact exp_one q hq k (fun j => g k j * g k j)
    have h2 : ∑ l ∈ Finset.univ.erase k,
        ∑ w : Fin n → I, (∏ m, q m (w m)) * (g k (w k) * g l (w l)) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [exp_two q hq k l (Finset.ne_of_mem_erase hl).symm (g k) (g l), hg0, zero_mul]
    rw [h1, h2, add_zero]
  calc ∑ w : Fin n → I, (∏ m, q m (w m)) * ((count w i : ℝ) - ∑ k, q k i) ^ 2
      = ∑ k : Fin n, ∑ l : Fin n, ∑ w : Fin n → I, (∏ m, q m (w m)) *
          (g k (w k) * g l (w l)) := by
        have e : ∀ w : Fin n → I, (∏ m, q m (w m)) * ((count w i : ℝ) - ∑ k, q k i) ^ 2 =
            ∑ k : Fin n, ∑ l : Fin n, (∏ m, q m (w m)) * (g k (w k) * g l (w l)) := by
          intro w; rw [hg, sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
        simp only [e]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, q k i * (1 - q k i) := Finset.sum_congr rfl fun k _ => key k

lemma total {n : ℕ} (q : Fin n → I → ℝ) (hq : ∀ i, ∑ j, q i j = 1) :
    ∑ w : Fin n → I, ∏ m, q m (w m) = 1 := by
  rw [← Fintype.prod_sum (fun (m : Fin n) (j : I) => q m j)]; simp [hq]

lemma W_nonneg {n : ℕ} (q : Fin n → I → ℝ) (hq0 : ∀ i j, 0 ≤ q i j) (w : Fin n → I) :
    0 ≤ ∏ m, q m (w m) := Finset.prod_nonneg fun m _ => hq0 _ _

/-- Chebyshev + union bound for the empirical counts. -/
lemma concentration {n : ℕ} (hn : 0 < n) (q : Fin n → I → ℝ) (hq0 : ∀ i j, 0 ≤ q i j)
    (hq : ∀ i, ∑ j, q i j = 1) (delta : ℝ) (hdelta : 0 < delta) :
    1 - 1 / delta ^ 2 ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ∀ i,
      |(count w i : ℝ) - ∑ k, q k i| ≤ delta * Real.sqrt n), ∏ m, q m (w m) := by
  set t := delta * Real.sqrt n
  have ht : 0 < t := mul_pos hdelta (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have ht2 : t ^ 2 = delta ^ 2 * n := by
    simp only [t]; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  set B : I → Finset (Fin n → I) := fun i => Finset.univ.filter (fun w : Fin n → I =>
    t < |(count w i : ℝ) - ∑ k, q k i|)
  have hbad : ∀ i, (∑ w ∈ B i, ∏ m, q m (w m)) * t ^ 2 ≤ ∑ k, q k i * (1 - q k i) := by
    intro i
    rw [← variance q hq i, Finset.sum_mul]
    calc ∑ w ∈ B i, (∏ m, q m (w m)) * t ^ 2
        ≤ ∑ w ∈ B i, (∏ m, q m (w m)) * ((count w i : ℝ) - ∑ k, q k i) ^ 2 := by
          refine Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left ?_ (W_nonneg q hq0 w)
          rw [Finset.mem_filter] at hw
          rw [← sq_abs ((count w i : ℝ) - ∑ k, q k i)]
          nlinarith [hw.2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun w _ _ => mul_nonneg (W_nonneg q hq0 w) (sq_nonneg _))
  have hsumV : ∑ i, ∑ k, q k i * (1 - q k i) ≤ n := by
    rw [Finset.sum_comm]
    calc ∑ k : Fin n, ∑ i, q k i * (1 - q k i) ≤ ∑ k : Fin n, ∑ i, q k i := by
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => ?_
          have : q k i ≤ 1 := by
            rw [← hq k]; exact Finset.single_le_sum (fun j _ => hq0 k j) (Finset.mem_univ i)
          nlinarith [hq0 k i]
      _ = n := by simp [hq]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - ∑ k, q k i| ≤ t) (fun w => ∏ m, q m (w m))
  rw [total q hq] at hsplit
  have hnot : ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ¬ ∀ i,
      |(count w i : ℝ) - ∑ k, q k i| ≤ t), ∏ m, q m (w m) ≤
      ∑ i, ∑ w ∈ B i, ∏ m, q m (w m) := by
    calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ¬ ∀ i,
          |(count w i : ℝ) - ∑ k, q k i| ≤ t),
          ∑ i, (if w ∈ B i then ∏ m, q m (w m) else 0) := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [Finset.mem_filter] at hw
          push Not at hw
          obtain ⟨i, hi⟩ := hw.2
          have : (if w ∈ B i then ∏ m, q m (w m) else 0) = ∏ m, q m (w m) := by
            rw [if_pos]; simp [B, hi]
          calc ∏ m, q m (w m) = (if w ∈ B i then ∏ m, q m (w m) else 0) := this.symm
            _ ≤ _ := Finset.single_le_sum
              (f := fun i => if w ∈ B i then ∏ m, q m (w m) else 0)
              (fun j _ => by split_ifs; exact W_nonneg q hq0 w; exact le_refl _)
              (Finset.mem_univ i)
      _ ≤ ∑ w : Fin n → I, ∑ i, (if w ∈ B i then ∏ m, q m (w m) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ =>
            Finset.sum_nonneg fun j _ => by split_ifs; exact W_nonneg q hq0 w; exact le_refl _)
      _ = ∑ i, ∑ w ∈ B i, ∏ m, q m (w m) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite_mem]; simp
  have hB : (∑ i, ∑ w ∈ B i, ∏ m, q m (w m)) * t ^ 2 ≤ n := by
    rw [Finset.sum_mul]
    exact (Finset.sum_le_sum fun i _ => hbad i).trans hsumV
  have hB' : ∑ i, ∑ w ∈ B i, ∏ m, q m (w m) ≤ 1 / delta ^ 2 := by
    rw [ht2] at hB
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ (by positivity)]
    have : (∑ i, ∑ w ∈ B i, ∏ m, q m (w m)) * delta ^ 2 * n ≤ 1 * n := by
      rw [mul_assoc]; linarith
    exact le_of_mul_le_mul_right this hn'
  linarith

end prob

section mat

variable {d : ℕ}

lemma wt_mul {n : ℕ} (A B : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    wordTensor A * wordTensor B = wordTensor (fun i => A i * B i) := by
  ext a b
  simp only [wordTensor, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_mul_distrib]

lemma wt_trace {n : ℕ} (C : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (wordTensor C).trace = ∏ i, (C i).trace := by
  simp only [Matrix.trace, Matrix.diag, wordTensor]
  rw [Fintype.prod_sum]

lemma atom_trace (S : FineResolution d) (M : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    (M * S.atom j).trace =
      star (fun a => (S.basis : Matrix (Fin d) (Fin d) ℂ) a j) ⬝ᵥ
        (M *ᵥ fun a => (S.basis : Matrix (Fin d) (Fin d) ℂ) a j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, FineResolution.atom, dotProduct,
    Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]; ring

lemma col_norm (S : FineResolution d) (j : Fin d) :
    ∑ a, ‖(S.basis : Matrix (Fin d) (Fin d) ℂ) a j‖ ^ 2 = 1 := by
  have hUU := Matrix.mem_unitaryGroup_iff'.mp S.basis.2
  have := congrFun (congrFun hUU j) j
  simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply] at this
  have e : ∀ a, star ((S.basis : Matrix (Fin d) (Fin d) ℂ) a j) *
      (S.basis : Matrix (Fin d) (Fin d) ℂ) a j =
      ((‖(S.basis : Matrix (Fin d) (Fin d) ℂ) a j‖ ^ 2 : ℝ) : ℂ) := by
    intro a; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  simp only [e] at this
  exact_mod_cast this

lemma atom_sum (S : FineResolution d) : ∑ j, S.atom j = 1 := by
  have hUU := Matrix.mem_unitaryGroup_iff.mp S.basis.2
  ext a b
  rw [Matrix.sum_apply]
  have := congrFun (congrFun hUU a) b
  simp only [Matrix.mul_apply, Matrix.star_apply] at this
  rw [← this]
  simp only [FineResolution.atom, Complex.star_def]

lemma state_atom (S : FineResolution d) (j : Fin d) :
    (S.state * S.atom j).trace = (S.weight j : ℂ) := by
  rw [atom_trace]
  set U := (S.basis : Matrix (Fin d) (Fin d) ℂ)
  have hUU := Matrix.mem_unitaryGroup_iff'.mp S.basis.2
  have hv : Uᴴ *ᵥ (fun a => U a j) = Pi.single j 1 := by
    ext k
    have := congrFun (congrFun hUU k) j
    simp only [Matrix.mul_apply, Matrix.star_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
    rw [this, Matrix.one_apply, Pi.single_apply]
  have hst : S.state = U * Matrix.diagonal (fun x => (S.weight x : ℂ)) * Uᴴ := rfl
  rw [hst, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.dotProduct_mulVec]
  rw [show (star fun a => U a j) ᵥ* U = star (Uᴴ *ᵥ fun a => U a j) by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
  rw [hv]
  simp [dotProduct, Matrix.mulVec, Matrix.diagonal_apply, Pi.single_apply]

lemma opnorm_bound (X : Matrix (Fin d) (Fin d) ℂ) (u : Fin d → ℂ) (hu : ∑ a, ‖u a‖ ^ 2 = 1) :
    ‖star u ⬝ᵥ (X *ᵥ u)‖ ≤ complexOperatorNorm X := by
  set x : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 u
  set f := (Matrix.toEuclideanLin X).toContinuousLinearMap
  have hx : ‖x‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simp [x, hu]
  have e : star u ⬝ᵥ (X *ᵥ u) = inner ℂ x (f x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
  rw [e]
  calc ‖inner ℂ x (f x)‖ ≤ ‖x‖ * ‖f x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖f‖ * ‖x‖) := mul_le_mul_of_nonneg_left (f.le_opNorm x) (norm_nonneg _)
    _ = complexOperatorNorm X := by rw [hx, one_mul, mul_one]; rfl

end mat

end X6TWL


noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Dependency50.P19 (count)

namespace X6TCT

variable {I : Type} [Fintype I] [DecidableEq I]

/-- expectation of a single coordinate under the product law. -/
lemma exp_one (p : I → ℝ) (hp : ∑ j, p j = 1) {n : ℕ} (k : Fin n) (a : I → ℝ) :
    ∑ w : Fin n → I, (∏ m, p (w m)) * a (w k) = ∑ j, p j * a j := by
  have h := (Fintype.prod_sum (fun (m : Fin n) (j : I) => p j * (if m = k then a j else 1))).symm
  have e1 : ∀ w : Fin n → I, ∏ m, p (w m) * (if m = k then a (w m) else 1) =
      (∏ m, p (w m)) * a (w k) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k (fun m => a (w m))]
    simp
  simp only [e1] at h
  rw [h]
  have e2 : ∀ m, ∑ j, p j * (if m = k then a j else 1) = if m = k then ∑ j, p j * a j else 1 := by
    intro m; split_ifs <;> simp [hp]
  simp only [e2]
  rw [Finset.prod_ite_eq' Finset.univ k (fun _ => ∑ j, p j * a j)]
  simp

/-- expectation of a product of two distinct coordinates. -/
lemma exp_two (p : I → ℝ) (hp : ∑ j, p j = 1) {n : ℕ} (k l : Fin n) (hkl : k ≠ l)
    (a b : I → ℝ) :
    ∑ w : Fin n → I, (∏ m, p (w m)) * (a (w k) * b (w l)) =
      (∑ j, p j * a j) * ∑ j, p j * b j := by
  have h := (Fintype.prod_sum (fun (m : Fin n) (j : I) =>
    p j * ((if m = k then a j else 1) * (if m = l then b j else 1)))).symm
  have e1 : ∀ w : Fin n → I, ∏ m, p (w m) * ((if m = k then a (w m) else 1) *
      (if m = l then b (w m) else 1)) = (∏ m, p (w m)) * (a (w k) * b (w l)) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ k (fun m => a (w m)),
      Finset.prod_ite_eq' Finset.univ l (fun m => b (w m))]
    simp
  simp only [e1] at h
  rw [h]
  have e2 : ∀ m, ∑ j, p j * ((if m = k then a j else 1) * (if m = l then b j else 1)) =
      (if m = k then ∑ j, p j * a j else 1) * (if m = l then ∑ j, p j * b j else 1) := by
    intro m
    by_cases h1 : m = k
    · have h2 : m ≠ l := h1 ▸ hkl
      simp [h1, hkl]
    · by_cases h2 : m = l
      · subst h2; simp [h1, Ne.symm hkl]
      · simp [h1, h2, hp]
  simp only [e2]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k (fun _ => ∑ j, p j * a j),
    Finset.prod_ite_eq' Finset.univ l (fun _ => ∑ j, p j * b j)]
  simp

lemma count_eq {n : ℕ} (w : Fin n → I) (i : I) :
    (count w i : ℝ) = ∑ k, (if w k = i then (1 : ℝ) else 0) := by
  unfold count
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- the variance of a letter count. -/
lemma variance (p : I → ℝ) (hp : ∑ j, p j = 1) (n : ℕ) (i : I) :
    ∑ w : Fin n → I, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 =
      n * (p i * (1 - p i)) := by
  set g : I → ℝ := fun j => (if j = i then 1 else 0) - p i
  have hg : ∀ w : Fin n → I, (count w i : ℝ) - n * p i = ∑ k, g (w k) := by
    intro w
    rw [count_eq]; simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hg0 : ∑ j, p j * g j = 0 := by
    simp only [g, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hp, one_mul, sub_self]
  have hg2 : ∑ j, p j * g j ^ 2 = p i * (1 - p i) := by
    have : ∀ j, p j * g j ^ 2 =
        (if j = i then p i * ((1 - p i) ^ 2 - p i ^ 2) else 0) + p j * p i ^ 2 := by
      intro j; simp only [g]; split_ifs with h
      · subst h; ring
      · ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.sum_mul, hp]
    ring
  have key : ∀ k : Fin n, ∑ l : Fin n, ∑ w : Fin n → I, (∏ m, p (w m)) * (g (w k) * g (w l)) =
      p i * (1 - p i) := by
    intro k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have h1 : ∑ w : Fin n → I, (∏ m, p (w m)) * (g (w k) * g (w k)) = p i * (1 - p i) := by
      rw [← hg2]
      have := exp_one p hp k (fun j => g j * g j)
      simp only [sq]; exact this
    have h2 : ∑ l ∈ Finset.univ.erase k,
        ∑ w : Fin n → I, (∏ m, p (w m)) * (g (w k) * g (w l)) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [exp_two p hp k l (Finset.ne_of_mem_erase hl).symm g g, hg0, zero_mul]
    rw [h1, h2, add_zero]
  calc ∑ w : Fin n → I, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2
      = ∑ k : Fin n, ∑ l : Fin n, ∑ w : Fin n → I, (∏ m, p (w m)) * (g (w k) * g (w l)) := by
        have e : ∀ w : Fin n → I, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 =
            ∑ k : Fin n, ∑ l : Fin n, (∏ m, p (w m)) * (g (w k) * g (w l)) := by
          intro w; rw [hg, sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
        simp only [e]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = n * (p i * (1 - p i)) := by
        simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma total (p : I → ℝ) (hp : ∑ j, p j = 1) (n : ℕ) :
    ∑ w : Fin n → I, ∏ m, p (w m) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : I) => p j)]; simp [hp]

lemma W_nonneg (p : I → ℝ) (hp0 : ∀ j, 0 ≤ p j) {n : ℕ} (w : Fin n → I) :
    0 ≤ ∏ m, p (w m) := Finset.prod_nonneg fun m _ => hp0 _

/-- Chebyshev for one letter. -/
lemma bad (p : I → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha : 0 < alpha) (i : I) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => alpha * Real.sqrt (p i * (1 - p i)) *
      Real.sqrt n < |(count w i : ℝ) - n * p i|), ∏ m, p (w m) ≤ 1 / alpha ^ 2 := by
  set v := p i * (1 - p i)
  have hv := variance p hp n i
  have hpi1 : p i ≤ 1 := by
    rw [← hp]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  have hv0 : 0 ≤ v := mul_nonneg (hp0 i) (by linarith)
  set F := Finset.univ.filter (fun w : Fin n → I => alpha * Real.sqrt v *
      Real.sqrt n < |(count w i : ℝ) - n * p i|)
  have hterm : ∀ w : Fin n → I, 0 ≤ (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 :=
    fun w => mul_nonneg (W_nonneg p hp0 w) (sq_nonneg _)
  have hsub : ∑ w ∈ F, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 ≤ n * v := by
    rw [← hv]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => hterm w)
  rcases hv0.lt_or_eq with hvpos | hvz
  · have ht2 : (alpha * Real.sqrt v * Real.sqrt n) ^ 2 = alpha ^ 2 * (n * v) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hv0, Real.sq_sqrt (Nat.cast_nonneg n)]; ring
    have hlow : (∑ w ∈ F, ∏ m, p (w m)) * (alpha ^ 2 * (n * v)) ≤
        ∑ w ∈ F, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun w hw => ?_
      rw [Finset.mem_filter] at hw
      refine mul_le_mul_of_nonneg_left ?_ (W_nonneg p hp0 w)
      rw [← ht2, ← sq_abs ((count w i : ℝ) - n * p i)]
      have h0 : 0 ≤ alpha * Real.sqrt v * Real.sqrt n := by positivity
      nlinarith [hw.2]
    have hnv : 0 < n * v := mul_pos (by exact_mod_cast hn) hvpos
    rw [le_div_iff₀ (by positivity)]
    have := hlow.trans hsub
    have h2 : (∑ w ∈ F, ∏ m, p (w m)) * alpha ^ 2 * (n * v) ≤ 1 * (n * v) := by
      rw [mul_assoc]; linarith
    exact le_of_mul_le_mul_right h2 hnv
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hterm w)).mp
      (by rw [hv]; change (n : ℝ) * v = 0; rw [← hvz, mul_zero])
    have : ∑ w ∈ F, ∏ m, p (w m) = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [Finset.mem_filter] at hw
      have h1 := hall w (Finset.mem_univ w)
      have h2 : 0 < ((count w i : ℝ) - n * p i) ^ 2 := by
        rw [← sq_abs]; have := hw.2; rw [← hvz] at this; simp at this; positivity
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · linarith
    rw [this]; positivity

/-- mass of the typical set. -/
lemma mass (p : I → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha : 0 < alpha) :
    1 - Fintype.card I / alpha ^ 2 ≤
      ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n), ∏ m, p (w m) := by
  set S := Finset.univ.filter (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n)
  set B : I → Finset (Fin n → I) := fun i => Finset.univ.filter (fun w : Fin n → I =>
    alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n < |(count w i : ℝ) - n * p i|)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n) (fun w => ∏ m, p (w m))
  rw [total p hp] at hsplit
  have hnot : ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ¬ ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n), ∏ m, p (w m) ≤
      ∑ i, ∑ w ∈ B i, ∏ m, p (w m) := by
    calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ¬ ∀ i, |(count w i : ℝ) - n * p i| ≤
          alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n),
          ∑ i, (if w ∈ B i then ∏ m, p (w m) else 0) := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [Finset.mem_filter] at hw
          push Not at hw
          obtain ⟨i, hi⟩ := hw.2
          have : (if w ∈ B i then ∏ m, p (w m) else 0) = ∏ m, p (w m) := by
            rw [if_pos]; simp [B, hi]
          calc ∏ m, p (w m) = (if w ∈ B i then ∏ m, p (w m) else 0) := this.symm
            _ ≤ _ := Finset.single_le_sum (f := fun i => if w ∈ B i then ∏ m, p (w m) else 0)
              (fun j _ => by split_ifs; exact W_nonneg p hp0 w; exact le_refl _) (Finset.mem_univ i)
      _ ≤ ∑ w : Fin n → I, ∑ i, (if w ∈ B i then ∏ m, p (w m) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ =>
            Finset.sum_nonneg fun j _ => by split_ifs; exact W_nonneg p hp0 w; exact le_refl _)
      _ = ∑ i, ∑ w ∈ B i, ∏ m, p (w m) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite_mem]; simp
  have hB : ∑ i, ∑ w ∈ B i, ∏ m, p (w m) ≤ Fintype.card I * (1 / alpha ^ 2) := by
    calc _ ≤ ∑ _i : I, 1 / alpha ^ 2 := Finset.sum_le_sum fun i _ => bad p hp0 hp n hn alpha halpha i
      _ = _ := by simp
  have : (Fintype.card I : ℝ) / alpha ^ 2 = Fintype.card I * (1 / alpha ^ 2) := by ring
  linarith

lemma sqrt_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.sqrt x * (-Real.log x) ≤ 2 / Real.exp 1 := by
  rcases h0.lt_or_eq with hx | hx
  · set s := Real.sqrt x
    have hs : 0 < s := Real.sqrt_pos.mpr hx
    have hlx : Real.log x = 2 * Real.log s := by
      rw [← Real.log_rpow hs, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.sq_sqrt h0]
    have he := Real.exp_pos 1
    have key := Real.log_le_sub_one_of_pos (show 0 < 1 / (Real.exp 1 * s) by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul (by positivity)
      (by positivity), Real.log_exp] at key
    rw [hlx]
    have : -Real.log s ≤ 1 / (Real.exp 1 * s) := by linarith
    have h2 : s * (-Real.log s) ≤ s * (1 / (Real.exp 1 * s)) := mul_le_mul_of_nonneg_left this hs.le
    rw [show s * (1 / (Real.exp 1 * s)) = 1 / Real.exp 1 by field_simp] at h2
    have : s * -(2 * Real.log s) = 2 * (s * (-Real.log s)) := by ring
    rw [this, show 2 / Real.exp 1 = 2 * (1 / Real.exp 1) by ring]
    linarith
  · subst hx; simp; positivity

lemma card_le (p : I → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (n : ℕ)
    (alpha : ℝ) (halpha : 0 < alpha) :
    ((Finset.univ.filter (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n)).card : ℝ) ≤
      Real.exp (n * (-∑ i, p i * Real.log (p i)) +
        alpha * Real.sqrt n * Fintype.card I * (2 / Real.exp 1)) := by
  set S := Finset.univ.filter (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n)
  set X := n * (-∑ i, p i * Real.log (p i)) + alpha * Real.sqrt n * Fintype.card I * (2 / Real.exp 1)
  have hp1 : ∀ i, p i ≤ 1 := fun i => by
    rw [← hp]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  have hW : ∀ w ∈ S, Real.exp (-X) ≤ ∏ m, p (w m) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hc := hw.2
    have hpos : ∀ k, 0 < p (w k) := by
      intro k
      by_contra hk
      have hz : p (w k) = 0 := le_antisymm (not_lt.mp hk) (hp0 _)
      have := hc (w k)
      rw [hz] at this; simp at this
      have h1 : 1 ≤ count w (w k) := by
        unfold count; exact Finset.card_pos.mpr ⟨k, by simp⟩
      omega
    have hWpos : 0 < ∏ m, p (w m) := Finset.prod_pos fun m _ => hpos m
    rw [← Real.exp_log hWpos, Real.exp_le_exp, Real.log_prod (fun m _ => (hpos m).ne')]
    have hfib : ∑ k, Real.log (p (w k)) = ∑ i, (count w i : ℝ) * Real.log (p i) := by
      rw [← Finset.sum_fiberwise Finset.univ w (fun k => Real.log (p (w k)))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => Real.log (p i)) (fun k hk => by
        rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [hfib]
    have hterm : ∀ i, (count w i : ℝ) * (-Real.log (p i)) ≤
        n * (-(p i * Real.log (p i))) + alpha * Real.sqrt n * (2 / Real.exp 1) := by
      intro i
      have hl : 0 ≤ -Real.log (p i) := by
        have := Real.log_nonpos (hp0 i) (hp1 i); linarith
      have hci : (count w i : ℝ) ≤ n * p i + alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n :=
        by have := (abs_le.mp (hc i)).2; linarith
      have hsq : Real.sqrt (p i * (1 - p i)) * (-Real.log (p i)) ≤ 2 / Real.exp 1 := by
        refine le_trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hl)
          (sqrt_log (hp0 i) (hp1 i))
        nlinarith [hp0 i, hp1 i]
      have h1 := mul_le_mul_of_nonneg_right hci hl
      have h2 : 0 ≤ alpha * Real.sqrt n := by positivity
      have h3 := mul_le_mul_of_nonneg_left hsq h2
      nlinarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum] at hsum
    simp only [X, Finset.sum_neg_distrib, mul_neg] at hsum ⊢
    have : ∑ i, (count w i : ℝ) * Real.log (p i) = -∑ i, (count w i : ℝ) * (-Real.log (p i)) := by
      simp [Finset.sum_neg_distrib]
    rw [this]; nlinarith
  have hmass : (S.card : ℝ) * Real.exp (-X) ≤ 1 := by
    calc (S.card : ℝ) * Real.exp (-X) = ∑ w ∈ S, Real.exp (-X) := by simp
      _ ≤ ∑ w ∈ S, ∏ m, p (w m) := Finset.sum_le_sum hW
      _ ≤ ∑ w : Fin n → I, ∏ m, p (w m) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => W_nonneg p hp0 w)
      _ = 1 := total p hp n
  rw [Real.exp_neg] at hmass
  have := Real.exp_pos X
  rwa [mul_inv_le_iff₀ this, one_mul] at hmass

end X6TCT


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

namespace X6TER

open X6TWL

variable {d : ℕ}

lemma law_eq (S : FineResolution d) (j : Fin d) : (S.law j).toReal = S.weight j := by
  simp [FineResolution.law, PMF.ofFintype_apply, ENNReal.toReal_ofReal (S.nonneg j)]

lemma atom_tr (S : FineResolution d) (j : Fin d) : (S.atom j).trace = 1 := by
  have := col_norm S j
  simp only [Matrix.trace, Matrix.diag, FineResolution.atom]
  rw [← Complex.ofReal_one, ← this, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj']; push_cast; rfl

/-- the word projector `P_w`. -/
def P {n : ℕ} (S : Fin n → FineResolution d) (w : Fin n → Fin d) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := wordTensor (fun i => (S i).atom (w i))

/-- the product vector of a word. -/
def vec {n : ℕ} (S : Fin n → FineResolution d) (w : Fin n → Fin d) : (Fin n → Fin d) → ℂ :=
  fun a => ∏ i, ((S i).basis : Matrix (Fin d) (Fin d) ℂ) (a i) (w i)

lemma P_tr_mul {n : ℕ} (S : Fin n → FineResolution d) (w : Fin n → Fin d)
    (M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    (P S w * M).trace = star (vec S w) ⬝ᵥ (M *ᵥ vec S w) := by
  rw [Matrix.trace_mul_comm]
  have e : ∀ a b, P S w a b = vec S w a * conj (vec S w b) := by
    intro a b
    simp only [P, wordTensor, FineResolution.atom, vec, map_prod, Finset.prod_mul_distrib]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, e, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]; ring

lemma P_tr {n : ℕ} (S : Fin n → FineResolution d) (w : Fin n → Fin d) : (P S w).trace = 1 := by
  rw [P, wt_trace]; simp [atom_tr]

/-- multilinearity of `wordTensor`. -/
lemma wt_sum {n : ℕ} (c : Fin n → Fin d → ℂ) (A : Fin n → Fin d → Matrix (Fin d) (Fin d) ℂ) :
    wordTensor (fun i => ∑ j, c i j • A i j) =
      ∑ w : Fin n → Fin d, (∏ i, c i (w i)) • wordTensor (fun i => A i (w i)) := by
  ext a b
  simp only [wordTensor, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib]

lemma state_eq (S : FineResolution d) :
    S.state = ∑ j, ((S.weight j : ℝ) : ℂ) • S.atom j := by
  ext a b
  simp only [FineResolution.state, QAlgorithms.Papers.Independent.Dependency50.P19.Spectrum.density,
    conjSuperop, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.smul_apply, FineResolution.atom, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp [Complex.star_def]; ring

lemma sum_P {n : ℕ} (S : Fin n → FineResolution d) : ∑ w, P S w = 1 := by
  have h := wt_sum (fun _ _ => (1 : ℂ)) (fun i j => (S i).atom j)
  simp only [one_smul, Finset.prod_const_one] at h
  simp only [P]
  rw [← h]
  simp only [atom_sum]
  ext a b
  simp only [wordTensor, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra hc; push Not at hc; exact hab (funext hc)
    rw [if_neg hab]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma rho_eq {n : ℕ} (S : Fin n → FineResolution d) :
    wordTensor (fun i => (S i).state) =
      ∑ w, ((∏ i, (S i).weight (w i) : ℝ) : ℂ) • P S w := by
  simp only [state_eq]
  rw [wt_sum]
  push_cast
  rfl

lemma prob_P {n : ℕ} (S : Fin n → FineResolution d) (w : Fin n → Fin d) :
    effectProb (wordTensor (fun i => (S i).state)) (P S w) = ∏ i, (S i).weight (w i) := by
  unfold effectProb
  rw [P, wt_mul, wt_trace]
  simp only [state_atom]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

end X6TER


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Dependency50.P19 (count)

namespace X6TCR

open Polynomial

section diag

variable {m : Type*} [Fintype m] [DecidableEq m]

lemma spec_sub (d : m → ℝ) : spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) ⊆ Set.range d := by
  intro μ hμ
  by_contra hc
  rw [spectrum.mem_iff] at hμ
  apply hμ
  have e : (μ • 1 : Matrix m m ℂ) = Matrix.diagonal (fun _ => (μ : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [Matrix.one_apply, h]
  rw [Algebra.algebraMap_eq_smul_one, e, Matrix.diagonal_sub,
    Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  simp only [isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
  intro h
  apply hc
  refine ⟨i, ?_⟩
  have := congrArg Complex.re h
  simpa using this.symm

lemma aeval_diag (d : m → ℝ) (P : ℝ[X]) :
    aeval (Matrix.diagonal (fun i => (d i : ℂ))) P =
      Matrix.diagonal (fun i => ((P.eval (d i) : ℝ) : ℂ)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.diagonal_add]
  | monomial k a =>
    rw [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, smul_one_mul,
      ← Matrix.diagonal_smul]
    congr 1; funext i
    simp only [eval_monomial, Pi.smul_apply, Pi.pow_apply, Complex.real_smul]
    push_cast; ring

lemma cfc_diag (d : m → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set S := Finset.univ.image d
  set P := Lagrange.interpolate S id f
  have hP : ∀ i, P.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    rwa [id] at this
  have hsa : IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  rw [cfc_congr (g := fun t => P.eval t), cfc_polynomial P _ hsa, aeval_diag]
  · congr 1; funext i; rw [hP]
  · intro t ht
    obtain ⟨i, rfl⟩ := spec_sub d ht
    exact (hP i).symm

end diag

lemma vn_state {d : ℕ} (S : FineResolution d) :
    vnEntropy S.state = -∑ j, S.weight j * Real.logb 2 (S.weight j) := by
  unfold vnEntropy
  set D := Matrix.diagonal (fun x => (S.weight x : ℂ))
  have hD : IsSelfAdjoint D := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) S.basis
  have hst : S.state = φ D := rfl
  have hφD : IsSelfAdjoint (φ D) := by
    rw [IsSelfAdjoint, ← map_star, hD.star_eq]
  have hcont : Continuous fun x : ℝ => x * Real.logb 2 x := by
    have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (x * Real.log x) / Real.log 2 := by
      funext x; rw [Real.logb]; ring
    rw [this]; exact Real.continuous_mul_log.div_const _
  rw [hst, ← StarAlgHomClass.map_cfc φ (fun x : ℝ => x * Real.logb 2 x) D
    hcont.continuousOn (by
      show Continuous fun x : Matrix (Fin d) (Fin d) ℂ =>
        (S.basis : Matrix (Fin d) (Fin d) ℂ) * x * star (S.basis : Matrix (Fin d) (Fin d) ℂ)
      exact (continuous_const.mul continuous_id).mul continuous_const) hD hφD, cfc_diag]
  simp only [φ, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem S.basis.2,
    Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp

/-! Elementary estimates for `φ(x) = -x log x`. -/

lemma phi_sub {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) :
    -(x + s) * Real.log (x + s) ≤ -x * Real.log x + -s * Real.log s := by
  rcases hx.lt_or_eq with hx | rfl
  · rcases hs.lt_or_eq with hs | rfl
    · have h1 : Real.log x ≤ Real.log (x + s) := Real.log_le_log hx (by linarith)
      have h2 : Real.log s ≤ Real.log (x + s) := Real.log_le_log hs (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h1 hx.le, mul_le_mul_of_nonneg_left h2 hs.le]
    · simp
  · simp

lemma phi_drop {q s : ℝ} (hq : 0 ≤ q) (hs : 0 ≤ s) (h1 : q + s ≤ 1) :
    -q * Real.log q - -(q + s) * Real.log (q + s) ≤ s := by
  have hl : Real.log (q + s) ≤ 0 := Real.log_nonpos (by linarith) h1
  rcases hq.lt_or_eq with hq | rfl
  · have key : Real.log (q + s) - Real.log q ≤ s / q := by
      rw [← Real.log_div (by linarith) hq.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < (q + s) / q by positivity)
      have e : (q + s) / q - 1 = s / q := by field_simp; ring
      linarith
    have h2 : q * (Real.log (q + s) - Real.log q) ≤ s := by
      have := mul_le_mul_of_nonneg_left key hq.le
      rwa [mul_div_cancel₀ _ hq.ne'] at this
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs hl]
  · rw [zero_add] at hl
    simp only [zero_add, neg_zero, zero_mul, zero_sub, neg_mul, neg_neg]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs hl]

lemma phi_ge {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ Real.exp (-1)) : s ≤ -s * Real.log s := by
  rcases hs.lt_or_eq with hs | rfl
  · have : Real.log s ≤ -1 := by
      have := Real.log_le_log hs hs1; rwa [Real.log_exp] at this
    nlinarith
  · simp

lemma phi_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ Real.exp (-1)) :
    -s * Real.log s ≤ -t * Real.log t := by
  rcases hs.lt_or_eq with hs | rfl
  · have htp : 0 < t := by linarith
    have hlt : Real.log t ≤ -1 := by
      have := Real.log_le_log htp ht; rwa [Real.log_exp] at this
    have key : Real.log t - Real.log s ≤ t / s - 1 := by
      rw [← Real.log_div htp.ne' hs.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have h2 : s * (Real.log t - Real.log s) ≤ t - s := by
      have := mul_le_mul_of_nonneg_left key hs.le
      have e : s * (t / s - 1) = t - s := by field_simp
      linarith
    nlinarith
  · simp only [neg_zero, zero_mul]
    have := phi_ge (le_trans hs hst) ht
    linarith

lemma phi_cont {p q t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hpq : |q - p| ≤ t) (ht : t ≤ Real.exp (-1)) :
    -q * Real.log q - -p * Real.log p ≤ -t * Real.log t := by
  rcases le_total p q with h | h
  · have hs : 0 ≤ q - p := by linarith
    have h1 := phi_sub hp0 hs
    rw [show p + (q - p) = q by ring] at h1
    have h2 := phi_mono hs (by rw [abs_of_nonneg hs] at hpq; exact hpq) ht
    linarith
  · have hs : 0 ≤ p - q := by linarith
    have h1 := phi_drop hq0 hs (by linarith)
    rw [show q + (p - q) = p by ring] at h1
    have hpq' : p - q ≤ t := by rw [abs_sub_comm, abs_of_nonneg hs] at hpq; exact hpq
    have h2 := phi_ge hs (le_trans hpq' ht)
    have h3 := phi_mono hs hpq' ht
    linarith

/-- counting words by type. -/
lemma card_le {d n : ℕ} (p : Fin d → ℝ) (tol E : ℝ)
    (H : ∀ r : Fin d → ℝ, (∀ j, 0 ≤ r j ∧ r j ≤ 1) → ∑ j, r j = 1 →
      (∀ j, |(n : ℝ) * r j - n * p j| ≤ tol) → ∑ j, -r j * Real.log (r j) ≤ E) :
    ((Finset.univ.filter fun w : Fin n → Fin d => ∀ j,
      |(count w j : ℝ) - n * p j| ≤ tol).card : ℝ) ≤ (n + 1 : ℝ) ^ d * Real.exp (n * E) := by
  set C := Finset.univ.filter fun w : Fin n → Fin d => ∀ j, |(count w j : ℝ) - n * p j| ≤ tol
  set τ : (Fin n → Fin d) → (Fin d → ℕ) := fun w j => count w j
  have hsum : ∀ w : Fin n → Fin d, ∑ j, count w j = n := by
    intro w
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin d))) (f := w) (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  rw [Finset.card_eq_sum_card_image τ C]
  have hfib : ∀ c ∈ C.image τ, ((C.filter fun w => τ w = c).card : ℝ) ≤ Real.exp (n * E) := by
    intro c hc
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.mp hc
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : (C.filter fun w => τ w = τ w0).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun a _ b _ => funext fun k => k.elim0
      calc _ ≤ (1 : ℝ) := by exact_mod_cast this
        _ = _ := by simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set r : Fin d → ℝ := fun j => (count w0 j : ℝ) / n
    have hr0 : ∀ j, 0 ≤ r j := fun j => by positivity
    have hr1 : ∑ j, r j = 1 := by
      simp only [r, ← Finset.sum_div]
      rw [div_eq_one_iff_eq hn'.ne']; exact_mod_cast hsum w0
    have hrle : ∀ j, r j ≤ 1 := fun j => by
      rw [← hr1]; exact Finset.single_le_sum (fun i _ => hr0 i) (Finset.mem_univ j)
    have hE := H r (fun j => ⟨hr0 j, hrle j⟩) hr1 (fun j => by
      have := (Finset.mem_filter.mp hw0).2 j
      simp only [r]; rwa [mul_div_cancel₀ _ hn'.ne'])
    -- each word of type `c` has probability `exp (-n Σ φ(r))` under `r^{⊗n}`
    have hW : ∀ w ∈ C.filter (fun w => τ w = τ w0),
        Real.exp (-(n * ∑ j, -r j * Real.log (r j))) = ∏ k, r (w k) := by
      intro w hw
      have hτ : ∀ j, count w j = count w0 j := fun j => congrFun (Finset.mem_filter.mp hw).2 j
      have hpos : ∀ k, 0 < r (w k) := by
        intro k
        simp only [r]
        have : 1 ≤ count w0 (w k) := by
          rw [← hτ]; unfold count; exact Finset.card_pos.mpr ⟨k, by simp⟩
        have : (1 : ℝ) ≤ count w0 (w k) := by exact_mod_cast this
        positivity
      rw [← Real.exp_log (Finset.prod_pos fun k _ => hpos k),
        Real.log_prod (fun k _ => (hpos k).ne')]
      congr 1
      rw [← Finset.sum_fiberwise Finset.univ w (fun k => Real.log (r (w k)))]
      have : ∀ j, ∑ k ∈ Finset.univ.filter (fun k => w k = j), Real.log (r (w k)) =
          (count w0 j : ℝ) * Real.log (r j) := by
        intro j
        rw [Finset.sum_congr rfl (g := fun _ => Real.log (r j)) (fun k hk => by
          rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const, nsmul_eq_mul, ← hτ]
        rfl
      simp only [this, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [r]; field_simp
    have hmass : ((C.filter fun w => τ w = τ w0).card : ℝ) *
        Real.exp (-(n * ∑ j, -r j * Real.log (r j))) ≤ 1 := by
      calc _ = ∑ w ∈ C.filter (fun w => τ w = τ w0),
            Real.exp (-(n * ∑ j, -r j * Real.log (r j))) := by simp
        _ = ∑ w ∈ C.filter (fun w => τ w = τ w0), ∏ k, r (w k) := Finset.sum_congr rfl hW
        _ ≤ ∑ w : Fin n → Fin d, ∏ k, r (w k) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun w _ _ => Finset.prod_nonneg fun k _ => hr0 _)
        _ = 1 := X6TWL.total (fun _ => r) (fun _ => hr1)
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul] at hmass
    exact hmass.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hE hn'.le))
  have himg : ((C.image τ).card : ℝ) ≤ (n + 1 : ℝ) ^ d := by
    have hsub : C.image τ ⊆ Fintype.piFinset (fun _ : Fin d => Finset.range (n + 1)) := by
      intro c hc
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hc
      rw [Fintype.mem_piFinset]; intro j
      rw [Finset.mem_range, Nat.lt_succ_iff, ← hsum w]
      exact Finset.single_le_sum (f := fun j => count w j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have := Finset.card_le_card hsub
    rw [Fintype.card_piFinset] at this
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  push_cast
  calc ∑ c ∈ C.image τ, ((C.filter fun w => τ w = c).card : ℝ)
      ≤ ∑ c ∈ C.image τ, Real.exp (n * E) := Finset.sum_le_sum hfib
    _ = ((C.image τ).card : ℝ) * Real.exp (n * E) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right himg (Real.exp_pos _).le

end X6TCR


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Dependency50.P19 (count)

namespace X6TVT

variable {I : Type} [Fintype I] [DecidableEq I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Hoeffding's lemma on a finite alphabet. -/
lemma hoeff1 (P : PMF I) (g : I → ℝ) (a : ℝ) (hg : ∀ j, a ≤ g j ∧ g j ≤ a + 1)
    (hmean : ∑ j, (P j).toReal * g j = 0) (s : ℝ) (hs : 0 < s) :
    ∑ j, (P j).toReal * Real.exp (s * g j) ≤ Real.exp (s ^ 2 / 8) := by
  have hm : AEMeasurable g P.toMeasure := (measurable_of_finite g).aemeasurable
  have hb : ∀ᵐ ω ∂P.toMeasure, g ω ∈ Set.Icc a (a + 1) :=
    MeasureTheory.ae_of_all _ fun ω => ⟨(hg ω).1, (hg ω).2⟩
  have hc : ∫ x, g x ∂P.toMeasure = 0 := by
    rw [PMF.integral_eq_sum]; simpa [smul_eq_mul] using hmean
  have h := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hm hb hc hs
  have e1 : ProbabilityTheory.mgf g P.toMeasure s = ∑ j, (P j).toReal * Real.exp (s * g j) := by
    rw [ProbabilityTheory.mgf, PMF.integral_eq_sum]; simp [smul_eq_mul]
  have e2 : ((‖a + 1 - a‖₊ / 2) ^ 2 * s ^ 2 / 2 : ℝ) = s ^ 2 / 8 := by
    rw [show a + 1 - a = 1 by ring]; simp; ring
  rw [e1] at h
  calc _ ≤ _ := h
    _ = _ := by rw [← e2]

/-- Chernoff bound for a sum of iid bounded mean-zero letters. -/
lemma chernoff (P : PMF I) (g : I → ℝ) (a : ℝ) (hg : ∀ j, a ≤ g j ∧ g j ≤ a + 1)
    (hmean : ∑ j, (P j).toReal * g j = 0) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => t ≤ ∑ k, g (w k)),
      ∏ m, (P (w m)).toReal ≤ Real.exp (-2 * t ^ 2 / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s := 4 * t / n
  have hs : 0 < s := by positivity
  have hW0 : ∀ w : Fin n → I, 0 ≤ ∏ m, (P (w m)).toReal :=
    fun w => Finset.prod_nonneg fun m _ => ENNReal.toReal_nonneg
  have hmgf : ∑ w : Fin n → I, (∏ m, (P (w m)).toReal) * Real.exp (s * ∑ k, g (w k)) ≤
      Real.exp (s ^ 2 / 8) ^ n := by
    have h := (Fintype.prod_sum (fun (_ : Fin n) (j : I) => (P j).toReal * Real.exp (s * g j))).symm
    have e : ∀ w : Fin n → I, ∏ m, (P (w m)).toReal * Real.exp (s * g (w m)) =
        (∏ m, (P (w m)).toReal) * Real.exp (s * ∑ k, g (w k)) := by
      intro w
      rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
    simp only [e] at h
    rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) (hoeff1 P g a hg hmean s hs) n
  calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => t ≤ ∑ k, g (w k)),
        (∏ m, (P (w m)).toReal) * Real.exp (s * (∑ k, g (w k) - t)) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_filter] at hw
        have : 1 ≤ Real.exp (s * (∑ k, g (w k) - t)) :=
          Real.one_le_exp (mul_nonneg hs.le (by linarith [hw.2]))
        nlinarith [hW0 w]
    _ ≤ ∑ w : Fin n → I, (∏ m, (P (w m)).toReal) * Real.exp (s * (∑ k, g (w k) - t)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun w _ _ => mul_nonneg (hW0 w) (Real.exp_pos _).le)
    _ = Real.exp (-(s * t)) * ∑ w : Fin n → I, (∏ m, (P (w m)).toReal) *
          Real.exp (s * ∑ k, g (w k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [mul_sub, sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ Real.exp (-(s * t)) * Real.exp (s ^ 2 / 8) ^ n :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-2 * t ^ 2 / n) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        simp only [s]
        field_simp
        ring

/-- two-sided tail for a letter count. -/
lemma count_tail (P : PMF I) (i : I) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => t < |(count w i : ℝ) - n * (P i).toReal|),
      ∏ m, (P (w m)).toReal ≤ 2 * Real.exp (-2 * t ^ 2 / n) := by
  set p := (P i).toReal
  have hsum1 : ∑ j, (P j).toReal = 1 := by
    have h1 : ∑ j, P j = 1 := by simpa using P.tsum_coe
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top P a), h1]; simp
  have hp1 : p ≤ 1 := by
    rw [← hsum1]; exact Finset.single_le_sum (fun j _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  set g : I → ℝ := fun j => (if j = i then 1 else 0) - p
  have hG : ∀ w : Fin n → I, (count w i : ℝ) - n * p = ∑ k, g (w k) := by
    intro w
    rw [X6TCT.count_eq]; simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hmean : ∑ j, (P j).toReal * g j = 0 := by
    simp only [g, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hsum1, one_mul]
    simp [p]
  have hmean' : ∑ j, (P j).toReal * (-g j) = 0 := by
    simp only [mul_neg, Finset.sum_neg_distrib, hmean, neg_zero]
  have h1 := chernoff P g (-p) (fun j => by simp only [g]; split_ifs <;> constructor <;> linarith)
    hmean n hn t ht
  have h2 := chernoff P (fun j => -g j) (p - 1)
    (fun j => by simp only [g]; split_ifs <;> constructor <;> linarith) hmean' n hn t ht
  have hW0 : ∀ w : Fin n → I, 0 ≤ ∏ m, (P (w m)).toReal :=
    fun w => Finset.prod_nonneg fun m _ => ENNReal.toReal_nonneg
  calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => t ≤ ∑ k, g (w k)),
        ∏ m, (P (w m)).toReal +
      ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => t ≤ ∑ k, -g (w k)),
        ∏ m, (P (w m)).toReal := by
        rw [← Finset.sum_union_inter]
        refine le_trans ?_ (le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => hW0 w))
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w _ _ => hW0 w)
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hw ⊢
        rw [hG] at hw
        rcases lt_abs.mp hw with h | h
        · left; linarith
        · right; rw [Finset.sum_neg_distrib]; linarith
    _ ≤ _ := by linarith

end X6TVT

namespace X6TVT

open X6TWL X6TER

variable {d : ℕ}

lemma atom_mul (S : FineResolution d) (j k : Fin d) :
    S.atom j * S.atom k = if j = k then S.atom j else 0 := by
  have hUU := Matrix.mem_unitaryGroup_iff'.mp S.basis.2
  have hjk := congrFun (congrFun hUU j) k
  simp only [Matrix.mul_apply, Matrix.star_apply] at hjk
  ext a b
  simp only [Matrix.mul_apply, FineResolution.atom]
  have : ∑ x, (S.basis : Matrix (Fin d) (Fin d) ℂ) a j * conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) x j) *
      ((S.basis : Matrix (Fin d) (Fin d) ℂ) x k * conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) b k)) =
      (S.basis : Matrix (Fin d) (Fin d) ℂ) a j * conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) b k) *
        ∑ x, star ((S.basis : Matrix (Fin d) (Fin d) ℂ) x j) * (S.basis : Matrix (Fin d) (Fin d) ℂ) x k := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def]; ring
  rw [this, hjk, Matrix.one_apply]
  split_ifs with h
  · subst h; simp [FineResolution.atom]
  · simp

lemma P_mul {n : ℕ} (S : Fin n → FineResolution d) (w v : Fin n → Fin d) :
    P S w * P S v = if w = v then P S w else 0 := by
  simp only [P]
  rw [wt_mul]
  simp only [atom_mul]
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, w i ≠ v i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    ext a b
    simp only [wordTensor, Matrix.zero_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma P_psd {n : ℕ} (S : Fin n → FineResolution d) (w : Fin n → Fin d) : (P S w).PosSemidef := by
  have e : P S w = Matrix.vecMulVec (vec S w) (star (vec S w)) := by
    ext a b
    simp only [P, wordTensor, FineResolution.atom, vec, Matrix.vecMulVec_apply, Pi.star_apply,
      Finset.prod_mul_distrib, star_prod]
    rfl
  rw [e]; exact Matrix.posSemidef_vecMulVec_self_star _

end X6TVT

namespace X6TVT

variable {d : ℕ}

/-- word probability bounds on the variance-typical set (natural logs). -/
lemma W_bounds (p : Fin d → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) {n : ℕ}
    (alpha : ℝ) (halpha : 0 < alpha) (w : Fin n → Fin d)
    (hw : ∀ i, |(count w i : ℝ) - n * p i| ≤ alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n) :
    Real.exp (n * ∑ i, p i * Real.log (p i) - alpha * Real.sqrt n * d * (2 / Real.exp 1)) ≤
      ∏ m, p (w m) ∧
    ∏ m, p (w m) ≤
      Real.exp (n * ∑ i, p i * Real.log (p i) + alpha * Real.sqrt n * d * (2 / Real.exp 1)) := by
  have hp1 : ∀ i, p i ≤ 1 := fun i => by
    rw [← hp]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  have hpos : ∀ k, 0 < p (w k) := by
    intro k
    by_contra hk
    have hz : p (w k) = 0 := le_antisymm (not_lt.mp hk) (hp0 _)
    have := hw (w k)
    rw [hz] at this; simp at this
    have h1 : 1 ≤ count w (w k) := by
      unfold count; exact Finset.card_pos.mpr ⟨k, by simp⟩
    omega
  have hWpos : 0 < ∏ m, p (w m) := Finset.prod_pos fun m _ => hpos m
  have hfib : Real.log (∏ m, p (w m)) = ∑ i, (count w i : ℝ) * Real.log (p i) := by
    rw [Real.log_prod (fun m _ => (hpos m).ne')]
    rw [← Finset.sum_fiberwise Finset.univ w (fun k => Real.log (p (w k)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => Real.log (p i)) (fun k hk => by
      rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const, nsmul_eq_mul]
    rfl
  have hdev : |Real.log (∏ m, p (w m)) - n * ∑ i, p i * Real.log (p i)| ≤
      alpha * Real.sqrt n * d * (2 / Real.exp 1) := by
    rw [hfib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ i, |(count w i : ℝ) * Real.log (p i) - n * (p i * Real.log (p i))| ≤
        alpha * Real.sqrt n * (2 / Real.exp 1) := by
      intro i
      have hl : 0 ≤ -Real.log (p i) := by
        have := Real.log_nonpos (hp0 i) (hp1 i); linarith
      rw [show (count w i : ℝ) * Real.log (p i) - n * (p i * Real.log (p i)) =
        ((count w i : ℝ) - n * p i) * Real.log (p i) by ring, abs_mul,
        abs_of_nonpos (by linarith : Real.log (p i) ≤ 0)]
      have hsq : Real.sqrt (p i * (1 - p i)) * (-Real.log (p i)) ≤ 2 / Real.exp 1 := by
        refine le_trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hl)
          (X6TCT.sqrt_log (hp0 i) (hp1 i))
        nlinarith [hp0 i, hp1 i]
      have h1 := mul_le_mul_of_nonneg_right (hw i) hl
      have h2 : 0 ≤ alpha * Real.sqrt n := by positivity
      have h3 := mul_le_mul_of_nonneg_left hsq h2
      nlinarith
    calc _ ≤ ∑ i, |(count w i : ℝ) * Real.log (p i) - n * (p i * Real.log (p i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, alpha * Real.sqrt n * (2 / Real.exp 1) := Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp; ring
  have := abs_le.mp hdev
  rw [← Real.exp_log hWpos]
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

/-- the tail mass outside the variance-typical set, per letter. -/
lemma bad_letter (P : PMF (Fin d)) (n : ℕ) (hn : 0 < n) (alpha : ℝ) (halpha : 0 < alpha) (i : Fin d) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin d => alpha * Real.sqrt ((P i).toReal *
      (1 - (P i).toReal)) * Real.sqrt n < |(count w i : ℝ) - n * (P i).toReal|),
      ∏ m, (P (w m)).toReal ≤
      if 0 < Real.sqrt ((P i).toReal * (1 - (P i).toReal)) then
        2 * Real.exp (-2 * alpha ^ 2 * ((P i).toReal * (1 - (P i).toReal))) else 0 := by
  set p : Fin d → ℝ := fun j => (P j).toReal
  have hp0 : ∀ j, 0 ≤ p j := fun j => ENNReal.toReal_nonneg
  have hp : ∑ j, p j = 1 := by
    have h1 : ∑ j, P j = 1 := by simpa using P.tsum_coe
    simp only [p]; rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top P a), h1]; simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set v := p i * (1 - p i)
  have hpi1 : p i ≤ 1 := by
    rw [← hp]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  have hv0 : 0 ≤ v := mul_nonneg (hp0 i) (by linarith)
  split_ifs with hv
  · have hvp : 0 < v := Real.sqrt_pos.mp hv
    have ht : 0 < alpha * Real.sqrt v * Real.sqrt n := by positivity
    have h := count_tail P i n hn _ ht
    have e : -2 * (alpha * Real.sqrt v * Real.sqrt n) ^ 2 / n = -2 * alpha ^ 2 * v := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hv0, Real.sq_sqrt hn'.le]; field_simp
    rw [e] at h
    exact h
  · have hvz : v = 0 := by
      have : Real.sqrt v = 0 := le_antisymm (not_lt.mp hv) (Real.sqrt_nonneg _)
      rwa [Real.sqrt_eq_zero hv0] at this
    have hvar := X6TCT.variance p hp n i
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ =>
      mul_nonneg (X6TCT.W_nonneg p hp0 w) (sq_nonneg _))).mp
      (by rw [hvar]; change (n : ℝ) * v = 0; rw [hvz, mul_zero])
    refine le_of_eq (Finset.sum_eq_zero fun w hw => ?_)
    rw [Finset.mem_filter] at hw
    have h1 := hall w (Finset.mem_univ w)
    have h2 : 0 < ((count w i : ℝ) - n * p i) ^ 2 := by
      rw [← sq_abs]; have := hw.2; change _ < |_ - _ * p i| at this
      rw [show v = 0 from hvz] at this; simp at this; positivity
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · linarith

end X6TVT

open X6TWL X6TER X6TVT
open QAlgorithms.Papers.Independent.Information100.P06 (Below)
open QAlgorithms.Papers.Independent.Information100.P60 (copies)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {d : ℕ} (S : FineResolution d) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha : 0 < alpha) :
    let Pi := varianceProjector S n alpha
    let correction := varianceConstant * d * alpha * Real.sqrt n
    effectProb (copies n S.state) Pi ≥ 1 - (d : ℝ) / alpha^2 ∧
    effectProb (copies n S.state) Pi ≥ 1 - varianceTail S alpha ∧
    Below ((exp2 (-n * vnEntropy S.state - correction) : ℂ) • Pi)
      (Pi * copies n S.state * Pi) ∧
    Below (Pi * copies n S.state * Pi)
      ((exp2 (-n * vnEntropy S.state + correction) : ℂ) • Pi) ∧
    Pi.trace.re ≤ exp2 (n * vnEntropy S.state + correction) ∧
    ∀ (B : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (eta : ℝ),
      IsShadow (copies n S.state) B eta →
      B.trace.re ≥ (eta - varianceTail S alpha) * exp2 (n * vnEntropy S.state - correction) := by
  intro Pi corr
  set Sc : Fin n → FineResolution d := fun _ => S
  set p : Fin d → ℝ := fun j => (S.law j).toReal
  have hpw : ∀ j, p j = S.weight j := fun j => law_eq S j
  have hp0 : ∀ j, 0 ≤ p j := fun j => ENNReal.toReal_nonneg
  have hp : ∑ j, p j = 1 := by simp only [hpw]; exact S.total
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set V := varianceSet S.law n alpha
  set W : (Fin n → Fin d) → ℝ := fun w => ∏ m, p (w m)
  have hW0 : ∀ w, 0 ≤ W w := fun w => X6TCT.W_nonneg p hp0 w
  have hW1 : ∑ w, W w = 1 := X6TCT.total p hp n
  have hρ : copies n S.state = wordTensor (fun i => (Sc i).state) := rfl
  have hPi : Pi = ∑ w ∈ V, P Sc w := rfl
  have hWS : ∀ w, (∏ i, (Sc i).weight (w i)) = W w := fun w => by simp only [Sc, W, hpw]
  have hprob : effectProb (copies n S.state) Pi = ∑ w ∈ V, W w := by
    rw [hρ, hPi]; unfold effectProb
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have := prob_P Sc w; unfold effectProb at this; rw [this, hWS]
  have htr : Pi.trace.re = (V.card : ℝ) := by
    rw [hPi, Matrix.trace_sum, Complex.re_sum]; simp [P_tr]
  -- constants
  set He := -∑ i, p i * Real.log (p i)
  set X := alpha * Real.sqrt n * d * (2 / Real.exp 1)
  have hl2 : Real.log 2 ≠ 0 := by positivity
  have hvn : Real.log 2 * vnEntropy S.state = He := by
    rw [X6TCR.vn_state]; simp only [He, hpw, Real.logb]
    rw [mul_neg, Finset.mul_sum]; congr 1
    exact Finset.sum_congr rfl fun i _ => by field_simp
  have hcorr : Real.log 2 * corr = X := by
    simp only [corr, X, varianceConstant, Real.logb, Real.log_exp]; field_simp
  have hexp2 : ∀ y, exp2 y = Real.exp (Real.log 2 * y) := fun y => by
    unfold exp2; rw [Real.rpow_def_of_pos (by norm_num)]
  have E1 : exp2 (-n * vnEntropy S.state - corr) = Real.exp (n * ∑ i, p i * Real.log (p i) - X) := by
    rw [hexp2]; congr 1
    rw [show Real.log 2 * (-n * vnEntropy S.state - corr) =
      -n * (Real.log 2 * vnEntropy S.state) - Real.log 2 * corr by ring, hvn, hcorr]; simp [He]
  have E2 : exp2 (-n * vnEntropy S.state + corr) = Real.exp (n * ∑ i, p i * Real.log (p i) + X) := by
    rw [hexp2]; congr 1
    rw [show Real.log 2 * (-n * vnEntropy S.state + corr) =
      -n * (Real.log 2 * vnEntropy S.state) + Real.log 2 * corr by ring, hvn, hcorr]; simp only [He]; ring
  have E3 : exp2 (n * vnEntropy S.state + corr) =
      Real.exp (n * (-∑ i, p i * Real.log (p i)) + alpha * Real.sqrt n * Fintype.card (Fin d) *
        (2 / Real.exp 1)) := by
    rw [hexp2]; congr 1
    rw [show Real.log 2 * (n * vnEntropy S.state + corr) =
      n * (Real.log 2 * vnEntropy S.state) + Real.log 2 * corr by ring, hvn, hcorr]
    simp [He, X]
  have E4 : exp2 (n * vnEntropy S.state - corr) = Real.exp (-(n * ∑ i, p i * Real.log (p i) + X)) := by
    rw [hexp2]; congr 1
    rw [show Real.log 2 * (n * vnEntropy S.state - corr) =
      n * (Real.log 2 * vnEntropy S.state) - Real.log 2 * corr by ring, hvn, hcorr]; simp only [He]; ring
  have hVeq : V = Finset.univ.filter (fun w : Fin n → Fin d => ∀ i, |(count w i : ℝ) - n * p i| ≤
      alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n) := by
    ext w; simp [V, varianceSet, p]
  have hVmem : ∀ w ∈ V, ∀ i, |(count w i : ℝ) - n * p i| ≤
      alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n := fun w hw => by
    rw [hVeq] at hw; exact (Finset.mem_filter.mp hw).2
  have hbd := fun w hw => W_bounds p hp0 hp alpha halpha w (hVmem w hw)
  -- tail mass
  have htail : 1 - varianceTail S alpha ≤ ∑ w ∈ V, W w := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ V) W
    have hfV : Finset.univ.filter (fun w => w ∈ V) = V := by ext w; simp
    rw [hfV, hW1] at hsplit
    set B : Fin d → Finset (Fin n → Fin d) := fun i => Finset.univ.filter (fun w : Fin n → Fin d =>
      alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n < |(count w i : ℝ) - n * p i|)
    have hnot : ∑ w ∈ Finset.univ.filter (fun w => w ∉ V), W w ≤ ∑ i, ∑ w ∈ B i, W w := by
      calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w => w ∉ V), ∑ i, (if w ∈ B i then W w else 0) := by
            refine Finset.sum_le_sum fun w hw => ?_
            rw [Finset.mem_filter] at hw
            have : ∃ i, w ∈ B i := by
              by_contra hc; push Not at hc
              apply hw.2
              rw [hVeq, Finset.mem_filter]
              refine ⟨Finset.mem_univ _, fun i => ?_⟩
              have := hc i
              simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
              exact this
            obtain ⟨i, hi⟩ := this
            calc W w = (if w ∈ B i then W w else 0) := by rw [if_pos hi]
              _ ≤ _ := Finset.single_le_sum (f := fun i => if w ∈ B i then W w else 0)
                  (fun j _ => by split_ifs; exact hW0 w; exact le_refl _) (Finset.mem_univ i)
        _ ≤ ∑ w : Fin n → Fin d, ∑ i, (if w ∈ B i then W w else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ =>
              Finset.sum_nonneg fun j _ => by split_ifs; exact hW0 w; exact le_refl _)
        _ = ∑ i, ∑ w ∈ B i, W w := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_ite_mem]; simp
    have hB : ∑ i, ∑ w ∈ B i, W w ≤ varianceTail S alpha := by
      have hb := fun i => bad_letter S.law n hn alpha halpha i
      calc ∑ i, ∑ w ∈ B i, W w ≤ ∑ i, (if 0 < Real.sqrt (p i * (1 - p i)) then
            2 * Real.exp (-2 * alpha ^ 2 * (p i * (1 - p i))) else 0) := Finset.sum_le_sum fun i _ => hb i
        _ ≤ ∑ i, (if 0 < Real.sqrt (p i * (1 - p i)) then
            2 * Real.exp (-2 * spectralMu S ^ 2 * alpha ^ 2) else 0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            split_ifs with hi
            · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
              have hsupp : (Finset.univ.filter fun j => 0 < Real.sqrt ((S.law j).toReal *
                  (1 - (S.law j).toReal))).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
              have hmu : spectralMu S = (Finset.univ.filter fun j => 0 < Real.sqrt ((S.law j).toReal *
                  (1 - (S.law j).toReal))).inf' hsupp
                  (fun j => Real.sqrt ((S.law j).toReal * (1 - (S.law j).toReal))) := by
                unfold spectralMu; simp only; rw [dif_pos hsupp]
              have hle : spectralMu S ≤ Real.sqrt (p i * (1 - p i)) := by
                rw [hmu]; exact Finset.inf'_le (fun j => Real.sqrt ((S.law j).toReal * (1 - (S.law j).toReal))) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
              have h0 : 0 ≤ spectralMu S := by
                rw [hmu]; exact (Finset.le_inf'_iff _ _).mpr fun j hj => Real.sqrt_nonneg _
              have hv0 : 0 ≤ p i * (1 - p i) := (Real.sqrt_pos.mp hi).le
              have : spectralMu S ^ 2 ≤ p i * (1 - p i) := by
                rw [← Real.sq_sqrt hv0]; exact pow_le_pow_left₀ h0 hle 2
              nlinarith [sq_nonneg alpha]
            · exact le_refl _
        _ = varianceTail S alpha := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            unfold varianceTail spectralN; ring
    linarith
  -- `Π ρ Π = Σ_V W P_w`
  have hPρP : Pi * copies n S.state * Pi = ∑ w ∈ V, ((W w : ℝ) : ℂ) • P Sc w := by
    rw [hρ, rho_eq, hPi]
    simp only [hWS]
    have h1 : (∑ u ∈ V, P Sc u) * (∑ w, ((W w : ℝ) : ℂ) • P Sc w) =
        ∑ u ∈ V, ((W u : ℝ) : ℂ) • P Sc u := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      simp only [Matrix.mul_smul, P_mul, smul_ite, smul_zero]
      rw [Finset.sum_ite_eq]; simp
    rw [h1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mul_sum]
    simp only [Matrix.smul_mul, P_mul, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq]; simp [hu]
  have hsmulPi : ∀ c : ℝ, (c : ℂ) • Pi = ∑ w ∈ V, (c : ℂ) • P Sc w := fun c => by
    rw [hPi, Finset.smul_sum]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprob, ge_iff_le]
    have := X6TCT.mass p hp0 hp n hn alpha halpha
    simp only [Fintype.card_fin] at this
    refine this.trans (le_of_eq (Finset.sum_congr ?_ fun _ _ => rfl))
    ext w; rw [hVeq]; simp only [Finset.mem_filter]
  · rw [hprob, ge_iff_le]; exact htail
  · -- lower sandwich
    unfold Below
    rw [hPρP, hsmulPi, ← Finset.sum_sub_distrib]
    refine Matrix.posSemidef_sum _ fun w hw => ?_
    rw [← sub_smul, ← Complex.ofReal_sub]
    refine (P_psd Sc w).smul ?_
    rw [Complex.zero_le_real, E1]; linarith [(hbd w hw).1]
  · -- upper sandwich
    unfold Below
    rw [hPρP, hsmulPi, ← Finset.sum_sub_distrib]
    refine Matrix.posSemidef_sum _ fun w hw => ?_
    rw [← sub_smul, ← Complex.ofReal_sub]
    refine (P_psd Sc w).smul ?_
    rw [Complex.zero_le_real, E2]; linarith [(hbd w hw).2]
  · -- rank bound
    rw [htr, E3, hVeq]
    have := X6TCT.card_le p hp0 hp n alpha halpha
    convert this using 4
  · -- shadow bound
    intro B eta ⟨hB, heta⟩
    set x : (Fin n → Fin d) → ℝ := fun w => (P Sc w * B).trace.re
    have hx0 : ∀ w, 0 ≤ x w := by
      intro w
      have := hB.1.dotProduct_mulVec_nonneg (vec Sc w)
      simp only [x]; rw [P_tr_mul]; exact (Complex.nonneg_iff.mp this).1
    have hx1 : ∀ w, x w ≤ 1 := by
      intro w
      have := hB.2.dotProduct_mulVec_nonneg (vec Sc w)
      rw [← P_tr_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, P_tr] at this
      have := (Complex.nonneg_iff.mp this).1
      simp only [Complex.sub_re, Complex.one_re] at this
      simp only [x]; linarith
    have hxs : ∑ w, x w = B.trace.re := by
      simp only [x]
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, sum_P, Matrix.one_mul]
    have hρB : effectProb (copies n S.state) B = ∑ w, W w * x w := by
      unfold effectProb
      rw [hρ, show wordTensor (fun i => (Sc i).state) = _ from rho_eq Sc, Finset.sum_mul,
        Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, hWS]
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ V)
      (fun w => W w * x w)
    have hfV : Finset.univ.filter (fun w => w ∈ V) = V := by ext w; simp
    rw [hfV] at hsplit
    set c := Real.exp (n * ∑ i, p i * Real.log (p i) + X)
    have hc : 0 < c := Real.exp_pos _
    have hA : ∑ w ∈ V, W w * x w ≤ c * B.trace.re := by
      calc ∑ w ∈ V, W w * x w ≤ ∑ w ∈ V, c * x w :=
            Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_right (hbd w hw).2 (hx0 w)
        _ = c * ∑ w ∈ V, x w := by rw [Finset.mul_sum]
        _ ≤ c * B.trace.re := by
            refine mul_le_mul_of_nonneg_left ?_ hc.le
            rw [← hxs]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun w _ _ => hx0 w)
    have hB2 : ∑ w ∈ Finset.univ.filter (fun w => w ∉ V), W w * x w ≤ varianceTail S alpha := by
      have hsplitW := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ V) W
      rw [hfV, hW1] at hsplitW
      calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w => w ∉ V), W w :=
            Finset.sum_le_sum fun w _ => by nlinarith [hx1 w, hW0 w]
        _ ≤ _ := by linarith
    have hη : eta ≤ c * B.trace.re + varianceTail S alpha := by
      have : effectProb (copies n S.state) B = ∑ w ∈ V, W w * x w +
          ∑ w ∈ Finset.univ.filter (fun w => w ∉ V), W w * x w := by rw [hρB, hsplit]
      linarith
    rw [E4, ge_iff_le]
    have hcinv : Real.exp (-(n * ∑ i, p i * Real.log (p i) + X)) * c = 1 := by
      simp only [c]; rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have := mul_le_mul_of_nonneg_left (show eta - varianceTail S alpha ≤ c * B.trace.re by linarith)
      (Real.exp_pos (-(n * ∑ i, p i * Real.log (p i) + X))).le
    rw [← mul_assoc, hcinv, one_mul] at this
    linarith
