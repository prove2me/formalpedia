-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.constantTypicalRank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:36:18.840507+00:00
-- url     : https://prove2.me/submissions/61b43f6d-d58a-4652-8c28-c1a661cde01b

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

open X6TWL X6TCR

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {d : ℕ} (S : FineResolution d) (n : ℕ) (hn : 0 < n)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ Real.sqrt n / (2 * d)) :
    (constantProjector S n delta).trace.re ≤ (n + 1 : ℝ)^d *
      exp2 (n * vnEntropy S.state + n * d * etaFunction (delta / Real.sqrt n)) := by
  set p : Fin d → ℝ := fun j => S.weight j
  have hlaw : ∀ j, ((S.law j).toReal) = S.weight j := by
    intro j
    simp [FineResolution.law, PMF.ofFintype_apply, ENNReal.toReal_ofReal (S.nonneg j)]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hsmall; linarith
    · exact h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set t := delta / Real.sqrt n
  have ht0 : 0 ≤ t := by positivity
  have ht : t ≤ 1 / (2 * d) := by
    simp only [t]; rw [div_le_iff₀ hsq]
    rw [le_div_iff₀ (by positivity)] at hsmall
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
  -- trace of the projector = number of typical words
  have htr : (constantProjector S n delta).trace.re =
      ((Finset.univ.filter fun w : Fin n → Fin d => ∀ j,
        |(count w j : ℝ) - n * p j| ≤ delta * Real.sqrt n).card : ℝ) := by
    unfold constantProjector
    rw [Matrix.trace_sum, Complex.re_sum]
    have hatom : ∀ j, (S.atom j).trace = 1 := by
      intro j
      have := col_norm S j
      simp only [Matrix.trace, Matrix.diag, FineResolution.atom]
      rw [← Complex.ofReal_one, ← this, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Complex.mul_conj']; push_cast; rfl
    simp only [wt_trace, hatom, Finset.prod_const_one, Complex.one_re, Finset.sum_const,
      nsmul_eq_mul, mul_one, hlaw, p]
  rw [htr]
  -- the entropy continuity estimate
  set E := ∑ j, -p j * Real.log (p j) + d * (-t * Real.log t)
  have hp0 : ∀ j, 0 ≤ p j := fun j => S.nonneg j
  have hp1 : ∑ j, p j = 1 := S.total
  have hple : ∀ j, p j ≤ 1 := fun j => by
    rw [← hp1]; exact Finset.single_le_sum (fun i _ => hp0 i) (Finset.mem_univ j)
  have hphit : 0 ≤ -t * Real.log t := by
    have : Real.log t ≤ 0 := Real.log_nonpos ht0 (by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      refine ht.trans ?_; rw [div_le_one (by positivity)]; linarith)
    nlinarith
  have H : ∀ r : Fin d → ℝ, (∀ j, 0 ≤ r j ∧ r j ≤ 1) → ∑ j, r j = 1 →
      (∀ j, |(n : ℝ) * r j - n * p j| ≤ delta * Real.sqrt n) →
      ∑ j, -r j * Real.log (r j) ≤ E := by
    intro r hr hrs hclose
    have hrt : ∀ j, |r j - p j| ≤ t := by
      intro j
      have := hclose j
      rw [← mul_sub, abs_mul, abs_of_pos hn'] at this
      have e : delta * Real.sqrt n = n * (delta / Real.sqrt n) := by
        field_simp; rw [Real.sq_sqrt hn'.le]
      rw [e] at this
      exact le_of_mul_le_mul_left this hn'
    rcases (Nat.succ_le_of_lt hd).eq_or_lt with h1 | h2
    · -- d = 1: both laws are the point mass
      subst h1
      have hr : r 0 = 1 := by simpa using hrs
      have hp : p 0 = 1 := by simpa using hp1
      simp only [E, Fin.sum_univ_one, hr, hp, Nat.cast_one, one_mul]
      simp; linarith
    · have ht4 : t ≤ Real.exp (-1) := by
        have h2' : (2 : ℝ) ≤ d := by exact_mod_cast h2
        have : 1 / (2 * (d : ℝ)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have he : (1 : ℝ) / 4 < Real.exp (-1) := by
          rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
          have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
        linarith
      have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
        phi_cont (hp0 j) (hple j) (hr j).1 (hr j).2 (hrt j) ht4
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at this
      simp only [E]; linarith
  refine (card_le p (delta * Real.sqrt n) E H).trans (le_of_eq ?_)
  congr 1
  unfold exp2 etaFunction
  rw [vn_state, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hl : Real.log 2 ≠ 0 := by positivity
  simp only [E, p, Real.logb, mul_div_assoc', Finset.sum_div, ← Finset.sum_neg_distrib]
  field_simp
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp
