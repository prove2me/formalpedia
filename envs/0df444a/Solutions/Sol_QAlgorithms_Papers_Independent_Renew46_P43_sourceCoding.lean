-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.sourceCoding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:00:03.963056+00:00
-- url     : https://prove2.me/submissions/0172ad74-841e-4443-bf8a-67c05609065d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_varianceTypical
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_schumacherScheme
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_strongSourceConverse

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

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

namespace X6FEF

variable {J K : Type} [Fintype J] [DecidableEq J] [Fintype K]

lemma tr_r1 (Y : Matrix J J ℂ) (u : J → ℂ) :
    (Y * Matrix.of (fun a b => u a * conj (u b))).trace = star u ⬝ᵥ (Y *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]; ring

/-- entanglement fidelity through a Kraus decomposition. -/
lemma fe_kraus (ρ : Matrix J J ℂ) (hρ : ρ.PosSemidef) (A : K → Matrix J J ℂ) (T : Superop J J)
    (hT : ∀ X, T X = ∑ k, A k * X * (A k)ᴴ) :
    sourceFe ρ T = ∑ k, Complex.normSq ((A k * ρ).trace) := by
  have h0 : (0 : Matrix J J ℂ) ≤ ρ := Matrix.nonneg_iff_posSemidef.mpr hρ
  set s := cfc Real.sqrt ρ
  have hss : s * s = ρ := by
    simp only [s]
    rw [← cfc_mul Real.sqrt Real.sqrt ρ]
    conv_rhs => rw [← cfc_id ℝ ρ]
    refine cfc_congr fun x hx => ?_
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)
  have hsh : sᴴ = s := by
    have : IsSelfAdjoint s := cfc_predicate _ _
    exact this
  set φ : J × J → ℂ := fun p => s p.2 p.1
  set ψ : K → J × J → ℂ := fun k p => (A k * s) p.2 p.1
  have hΦ : purification ρ = Matrix.of (fun p q => φ p * conj (φ q)) := rfl
  have hM : idTensorSuperop (R := J) T (purification ρ) =
      ∑ k, Matrix.of (fun p q => ψ k p * conj (ψ k q)) := by
    ext p q
    simp only [idTensorSuperop, Matrix.of_apply, hT, hΦ, Matrix.sum_apply, ψ, φ]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold sourceFe effectProb
  rw [hM, hΦ, tr_r1]
  have hip : ∀ k, star φ ⬝ᵥ ψ k = (A k * ρ).trace := by
    intro k
    calc star φ ⬝ᵥ ψ k = (sᴴ * (A k * s)).trace := by
          simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, φ, ψ, Matrix.trace, Matrix.diag,
            Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = (A k * ρ).trace := by rw [hsh, Matrix.trace_mul_comm, Matrix.mul_assoc, hss]
  have : (∑ k, Matrix.of (fun p q => ψ k p * conj (ψ k q)) : Matrix (J × J) (J × J) ℂ) =
      Matrix.of (fun p q => ∑ k, ψ k p * conj (ψ k q)) := by
    ext p q; simp [Matrix.sum_apply]
  rw [this]
  have e2 : star φ ⬝ᵥ (Matrix.of (fun p q => ∑ k, ψ k p * conj (ψ k q)) *ᵥ φ) =
      ∑ k, (star φ ⬝ᵥ ψ k) * conj (star φ ⬝ᵥ ψ k) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.sum_mul,
      Finset.mul_sum, map_sum, map_mul, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [e2, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hip, Complex.mul_conj]; simp

lemma qf_kraus1 (A : Matrix J J ℂ) (u : J → ℂ) :
    star u ⬝ᵥ ((A * Matrix.of (fun a b => u a * conj (u b)) * Aᴴ) *ᵥ u) =
      (star u ⬝ᵥ (A *ᵥ u)) * conj (star u ⬝ᵥ (A *ᵥ u)) := by
  have e : A * Matrix.of (fun a b => u a * conj (u b)) * Aᴴ =
      Matrix.of (fun a b => (A *ᵥ u) a * conj ((A *ᵥ u) b)) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
      map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  set x := A *ᵥ u
  have lhs : star u ⬝ᵥ (Matrix.of (fun a b => x a * conj (x b)) *ᵥ u) =
      ∑ a, ∑ b, conj (u a) * x a * (conj (x b) * u b) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [lhs, ← Finset.sum_mul_sum]
  simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Complex.star_def, Complex.conj_conj]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma jensen {W : Type} [Fintype W] (q : W → ℝ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (z : W → ℂ) : Complex.normSq (∑ w, (q w : ℂ) * z w) ≤ ∑ w, q w * Complex.normSq (z w) := by
  have h1 : ‖∑ w, (q w : ℂ) * z w‖ ≤ ∑ w, q w * ‖z w‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hq0 w)]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => Real.sqrt (q w))
    (fun w => Real.sqrt (q w) * ‖z w‖)
  have e1 : ∀ w, Real.sqrt (q w) * (Real.sqrt (q w) * ‖z w‖) = q w * ‖z w‖ := by
    intro w; rw [← mul_assoc, Real.mul_self_sqrt (hq0 w)]
  have e2 : ∀ w, Real.sqrt (q w) ^ 2 = q w := fun w => Real.sq_sqrt (hq0 w)
  have e3 : ∀ w, (Real.sqrt (q w) * ‖z w‖) ^ 2 = q w * ‖z w‖ ^ 2 := by
    intro w; rw [mul_pow, Real.sq_sqrt (hq0 w)]
  simp only [e1, e2, e3, hq1, one_mul] at cs
  rw [Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ w, (q w : ℂ) * z w‖ ^ 2 ≤ (∑ w, q w * ‖z w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := cs

/-- entanglement fidelity is at most the ensemble-average fidelity. -/
lemma fe_le {W : Type} [Fintype W] (A : K → Matrix J J ℂ) (q : W → ℝ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (u : W → J → ℂ) (ρ : Matrix J J ℂ)
    (hρ : ρ = ∑ w, (q w : ℂ) • Matrix.of (fun a b => u w a * conj (u w b))) :
    ∑ k, Complex.normSq ((A k * ρ).trace) ≤
      ∑ w, q w * ((∑ k, A k * Matrix.of (fun a b => u w a * conj (u w b)) * (A k)ᴴ) *
        Matrix.of (fun a b => u w a * conj (u w b))).trace.re := by
  have htr : ∀ k, (A k * ρ).trace = ∑ w, (q w : ℂ) * (star (u w) ⬝ᵥ (A k *ᵥ u w)) := by
    intro k
    rw [hρ, Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, tr_r1, smul_eq_mul]
  have hR : ∀ w, ((∑ k, A k * Matrix.of (fun a b => u w a * conj (u w b)) * (A k)ᴴ) *
      Matrix.of (fun a b => u w a * conj (u w b))).trace.re =
      ∑ k, Complex.normSq (star (u w) ⬝ᵥ (A k *ᵥ u w)) := by
    intro w
    rw [tr_r1, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [qf_kraus1, Complex.mul_conj, Complex.ofReal_re]
  simp only [hR, htr, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun k _ => jensen q hq0 hq1 _

end X6FEF


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Information100.P60 (copies)

namespace X6SRC

variable {a d n : ℕ}

lemma law_sum (S : PureSource a d) : ∑ x, (S.law x).toReal = 1 := by
  have h := S.law.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ _), h]; simp

lemma weight_nonneg (S : PureSource a d) (w : Fin n → Fin a) : 0 ≤ S.weight w :=
  Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

lemma weight_sum (S : PureSource a d) : ∑ w : Fin n → Fin a, S.weight w = 1 :=
  X6TWL.total (fun _ x => (S.law x).toReal) (fun _ => law_sum S)

lemma copies_eq (S : PureSource a d) :
    copies n S.average = ∑ w : Fin n → Fin a, ((S.weight w : ℝ) : ℂ) • S.word w := by
  ext x y
  simp only [copies, PureSource.average, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [PureSource.weight, PureSource.word, wordTensor, Finset.prod_mul_distrib]
  push_cast; rfl

lemma word_vec (S : PureSource a d) : ∃ u : (Fin n → Fin a) → (Fin n → Fin d) → ℂ,
    (∀ w, S.word w = Matrix.of (fun x y => u w x * conj (u w y))) ∧
    (∀ w, ∑ b, ‖u w b‖ ^ 2 = 1) := by
  choose vx hvx1 hvx using S.pure
  refine ⟨fun w b => ∏ i, vx (w i) (b i), ?_, ?_⟩
  · intro w; ext x y
    simp only [PureSource.word, wordTensor, hvx, pureDensity, Matrix.of_apply, map_prod,
      Finset.prod_mul_distrib]
  · have hv1 : ∀ x, ∑ j, ‖vx x j‖ ^ 2 = 1 := by
      intro x
      have h := hvx1 x
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
      exact h
    intro w
    simp only [norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun i j => ‖vx (w i) j‖ ^ 2)]
    simp [hv1]

lemma r1_psd {J : Type} [Fintype J] (u : J → ℂ) : (Matrix.of (fun x y => u x * conj (u y))).PosSemidef := by
  have : Matrix.of (fun x y => u x * conj (u y)) = Matrix.vecMulVec u (star u) := by
    ext i j; simp [Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

lemma copies_psd (S : PureSource a d) : (copies n S.average).PosSemidef := by
  obtain ⟨u, hw, -⟩ := word_vec (n := n) S
  rw [copies_eq]
  refine Matrix.posSemidef_sum _ fun w _ => ?_
  rw [hw]
  exact (r1_psd _).smul (by exact_mod_cast weight_nonneg S w)

/-- entanglement fidelity of any extended code is at most its average fidelity. -/
lemma code_fe_le (S : PureSource a d) (c : SourceCode S n) (E : Superop (Fin n → Fin d) (Fin c.dim))
    (hE : EncoderExtension c E) :
    sourceFe (copies n S.average) (c.decode ∘ E) ≤ c.fidelity := by
  obtain ⟨m, R, hR, hD⟩ := c.decoder_channel
  obtain ⟨m', B, hB, hEk⟩ := hE.1
  set A : Fin m × Fin m' → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := fun p => R p.1 * B p.2
  have hT : ∀ X, (c.decode ∘ E) X = ∑ p, A p * X * (A p)ᴴ := by
    intro X
    simp only [Function.comp_apply, hD, hEk, krausApply, A, Fintype.sum_prod_type,
      Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  rw [X6FEF.fe_kraus _ (copies_psd S) A _ hT]
  obtain ⟨u, hw, -⟩ := word_vec (n := n) S
  have hρ : copies n S.average = ∑ w, ((S.weight w : ℝ) : ℂ) • Matrix.of (fun x y => u w x * conj (u w y)) := by
    rw [copies_eq]; simp only [hw]
  refine (X6FEF.fe_le A (fun w => S.weight w) (weight_nonneg S) (weight_sum S) u _ hρ).trans
    (le_of_eq ?_)
  unfold SourceCode.fidelity effectProb
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 3
  rw [← hT, hw, Function.comp_apply, ← hw, hE.2]

end X6SRC


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

namespace X6ACH

section gen

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]

lemma isChannel_of {K : Type} [Fintype K] (A : K → Matrix κ ι ℂ) (hA : ∑ k, (A k)ᴴ * A k = 1)
    (Φ : Superop ι κ) (hΦ : ∀ ρ, Φ ρ = ∑ k, A k * ρ * (A k)ᴴ) : IsChannel Φ := by
  set e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun i => A (e.symm i), ?_, fun ρ => ?_⟩
  · unfold IsKrausFamily
    rw [← hA]
    exact Equiv.sum_comp e.symm (fun k => (A k)ᴴ * A k)
  · rw [hΦ]; unfold krausApply
    exact (Equiv.sum_comp e.symm (fun k => A k * ρ * (A k)ᴴ)).symm

lemma channel_density (Φ : Superop ι κ) (hΦ : IsChannel Φ) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (Φ ρ) := by
  obtain ⟨m, E, hE, hEq⟩ := hΦ
  rw [hEq]; unfold krausApply
  refine ⟨Matrix.posSemidef_sum _ fun k _ => hρ.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_mul_comm _ (E _)ᴴ, ← Matrix.mul_assoc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hE
  rw [hE, Matrix.one_mul]; exact hρ.2

end gen

section iso

open X6TWL X6TER

variable {d n : ℕ}

lemma vec_orth (S : Fin n → FineResolution d) (w w' : Fin n → Fin d) :
    ∑ b, star (vec S w b) * vec S w' b = if w = w' then 1 else 0 := by
  simp only [vec, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i j => star (((S i).basis : Matrix (Fin d) (Fin d) ℂ) j (w i)) *
    ((S i).basis : Matrix (Fin d) (Fin d) ℂ) j (w' i))]
  have hU : ∀ i x y, ∑ j, star (((S i).basis : Matrix (Fin d) (Fin d) ℂ) j x) *
      ((S i).basis : Matrix (Fin d) (Fin d) ℂ) j y = if x = y then 1 else 0 := by
    intro i x y
    have hUU := Matrix.mem_unitaryGroup_iff'.mp (S i).basis.2
    have := congrFun (congrFun hUU x) y
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at this
    exact this
  simp only [hU]
  by_cases h : w = w'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ w' i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma P_eq (S : Fin n → FineResolution d) (w : Fin n → Fin d) (b b' : Fin n → Fin d) :
    P S w b b' = vec S w b * star (vec S w b') := by
  simp only [P, wordTensor, FineResolution.atom, vec, star_prod, Finset.prod_mul_distrib]
  rfl

variable (S : Fin n → FineResolution d) (Vs : Finset (Fin n → Fin d))

/-- the isometry onto the span of the word vectors of `Vs`. -/
def isoV : Matrix (Fin n → Fin d) (Fin Vs.card) ℂ :=
  fun b j => vec S (Vs.equivFin.symm j) b

lemma isoV_iso : (isoV S Vs)ᴴ * isoV S Vs = 1 := by
  ext j j'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, isoV, vec_orth, Matrix.one_apply]
  congr 1
  apply propext
  constructor
  · intro h; exact Vs.equivFin.symm.injective (Subtype.ext h)
  · intro h; rw [h]

lemma isoV_range : isoV S Vs * (isoV S Vs)ᴴ = ∑ w ∈ Vs, P S w := by
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, isoV, Matrix.sum_apply, P_eq]
  rw [← Finset.sum_coe_sort Vs]
  exact Equiv.sum_comp Vs.equivFin.symm (fun w : Vs => vec S w b * star (vec S w b'))

end iso

section pe

open X6TWL X6TER

variable {d n : ℕ} (S : Fin n → FineResolution d) (Vs : Finset (Fin n → Fin d))

/-- Kraus operators of the projection encoder. -/
def kr : Option (Fin Vs.card × {w : Fin n → Fin d // w ∉ Vs}) →
    Matrix (Fin Vs.card) (Fin n → Fin d) ℂ
  | none => (isoV S Vs)ᴴ
  | some (j, w) => Matrix.of fun j' b =>
      if j' = j then (((Real.sqrt Vs.card)⁻¹ : ℝ) : ℂ) * star (vec S w.1 b) else 0

lemma compl_sum : ∑ w : {w : Fin n → Fin d // w ∉ Vs}, P S w.1 = 1 - ∑ w ∈ Vs, P S w := by
  have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ Vs) (P S)
  rw [sum_P] at this
  have hfV : Finset.univ.filter (fun w => w ∈ Vs) = Vs := by ext w; simp
  rw [hfV] at this
  rw [← this, add_sub_cancel_left]
  exact (Finset.sum_subtype _ (fun w => by simp) (P S)).symm

lemma kr_some_mul (hk : 0 < Vs.card) (w : {w : Fin n → Fin d // w ∉ Vs}) :
    ∑ j : Fin Vs.card, (kr S Vs (some (j, w)))ᴴ * kr S Vs (some (j, w)) = P S w.1 := by
  ext b b'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, kr, Matrix.of_apply, P_eq]
  have hc : ∀ j : Fin Vs.card, ∑ j', star (if j' = j then (((Real.sqrt Vs.card)⁻¹ : ℝ) : ℂ) *
      star (vec S w.1 b) else 0) * (if j' = j then (((Real.sqrt Vs.card)⁻¹ : ℝ) : ℂ) *
      star (vec S w.1 b') else 0) = (((Vs.card : ℝ)⁻¹ : ℝ) : ℂ) * (vec S w.1 b * star (vec S w.1 b')) := by
    intro j
    rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
    simp only [if_true, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    have hk' : (0 : ℝ) < Vs.card := by exact_mod_cast hk
    have : ((Real.sqrt Vs.card)⁻¹ : ℝ) * (Real.sqrt Vs.card)⁻¹ = (Vs.card : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hk'.le]
    rw [← this]; push_cast; ring
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hk' : (Vs.card : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

lemma kr_norm (hk : 0 < Vs.card) : ∑ o, (kr S Vs o)ᴴ * kr S Vs o = 1 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have : (kr S Vs none)ᴴ * kr S Vs none = ∑ w ∈ Vs, P S w := by
    simp only [kr, Matrix.conjTranspose_conjTranspose]; exact isoV_range S Vs
  rw [this, Finset.sum_comm]
  simp only [kr_some_mul S Vs hk]
  rw [compl_sum]; abel

def cw (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (w : Fin n → Fin d) : ℂ :=
  ∑ b, ∑ b', star (vec S w b) * ρ b b' * vec S w b'

lemma kr_some_apply (hk : 0 < Vs.card) (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
    (w : {w : Fin n → Fin d // w ∉ Vs}) :
    ∑ j : Fin Vs.card, kr S Vs (some (j, w)) * ρ * (kr S Vs (some (j, w)))ᴴ =
      (cw S ρ w.1 / Vs.card) • (1 : Matrix (Fin Vs.card) (Fin Vs.card) ℂ) := by
  have hk' : (0 : ℝ) < Vs.card := by exact_mod_cast hk
  have hs : ((((Real.sqrt Vs.card)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt Vs.card)⁻¹ : ℝ) : ℂ) = 1 / (Vs.card : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hk'.le]; push_cast; ring
  ext j1 j2
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, kr, Matrix.of_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j1 (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  by_cases h : j2 = j1
  · subst h
    simp only [if_true, mul_one, cw]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    rw [div_eq_mul_one_div, ← hs]; ring
  · simp [h, Ne.symm h]

lemma cw_sum (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    ∑ w : {w : Fin n → Fin d // w ∉ Vs}, cw S ρ w.1 = ρ.trace - (ρ * ∑ w ∈ Vs, P S w).trace := by
  have e : ρ.trace - (ρ * ∑ w ∈ Vs, P S w).trace = (ρ * (1 - ∑ w ∈ Vs, P S w)).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one]
  rw [e, ← compl_sum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [cw, Matrix.trace, Matrix.diag, Matrix.mul_apply, P_eq]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring

lemma pe_channel (hk : 0 < Vs.card) : IsChannel (projectionEncoder (isoV S Vs)) := by
  refine isChannel_of (kr S Vs) (kr_norm S Vs hk) _ fun ρ => ?_
  rw [Fintype.sum_option, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [kr_some_apply S Vs hk]
  rw [← Finset.sum_smul, ← Finset.sum_div, cw_sum, ← isoV_range]
  simp only [projectionEncoder, kr, Matrix.conjTranspose_conjTranspose]

end pe

end X6ACH


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Information100.P60 (copies)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X6ACH

open X6TER

theorem achieve {a d : ℕ} (S : PureSource a d) (sp : FineResolution d) (hsp : sp.state = S.average)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (hα : 0 < α) (hne : 0 < (varianceSet sp.law n α).card) :
    ∃ c : SourceCode S n, ∃ E, EncoderExtension c E ∧
      sourceFe (copies n S.average) (c.decode ∘ E) ≥ 1 - 2 * varianceTail sp α ∧
      c.rate ≤ vnEntropy S.average + varianceConstant * d * α / Real.sqrt n := by
  set Vs := varianceSet sp.law n α
  set Sc : Fin n → FineResolution d := fun _ => sp
  set V := isoV Sc Vs
  have hiso : Vᴴ * V = 1 := isoV_iso Sc Vs
  have hrange : V * Vᴴ = varianceProjector sp n α := isoV_range Sc Vs
  obtain ⟨u, hw, hu⟩ := X6SRC.word_vec (n := n) S
  have hdens : ∀ w : Fin n → Fin a, IsDensityMatrix (S.word w) := by
    intro w
    rw [hw]
    refine ⟨X6SRC.r1_psd _, ?_⟩
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast hu w
  have hPE := pe_channel Sc Vs hne
  let c : SourceCode S n :=
    { length_pos := hn
      dim := Vs.card
      dim_pos := hne
      encode := fun w => projectionEncoder V (S.word w)
      encoded_state := fun w => channel_density _ hPE _ (hdens w)
      decode := conjSuperop V
      decoder_channel := ⟨1, fun _ => V, by unfold IsKrausFamily; simp [hiso],
        fun ρ => by simp [krausApply, conjSuperop]⟩ }
  have hsch := schumacherScheme S sp hsp n hn α hα Vs.card hne V hiso hrange
  refine ⟨c, projectionEncoder V, ⟨hPE, fun w => rfl⟩, hsch.2, hsch.1⟩

end X6ACH


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open Filter

namespace X6CV

lemma exists_res {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) (htr : A.trace = 1) :
    ∃ S : FineResolution d, S.state = A := by
  refine ⟨⟨hA.1.eigenvalues, hA.eigenvalues_nonneg, ?_, hA.1.eigenvectorUnitary⟩, ?_⟩
  · have h := hA.1.trace_eq_sum_eigenvalues
    rw [htr] at h
    have := congrArg Complex.re h
    simpa using this.symm
  · conv_rhs => rw [hA.1.spectral_theorem]
    simp only [FineResolution.state, QAlgorithms.Papers.Independent.Dependency50.P19.Spectrum.density,
      conjSuperop, Unitary.conjStarAlgAut_apply]
    rfl

lemma average_psd {a d : ℕ} (S : PureSource a d) : S.average.PosSemidef ∧ S.average.trace = 1 := by
  choose vx hvx1 hvx using S.pure
  have hl : ∑ x, (S.law x).toReal = 1 := by
    have h := S.law.tsum_coe
    rw [tsum_fintype] at h
    rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ _), h]; simp
  have hpd : ∀ x, (S.letter x).PosSemidef := by
    intro x; rw [hvx]
    have : pureDensity (vx x) = Matrix.vecMulVec (vx x).ofLp (star (vx x).ofLp) := by
      ext i j; simp [pureDensity, Matrix.vecMulVec_apply]
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  have htr : ∀ x, (S.letter x).trace = 1 := by
    intro x; rw [hvx]
    have h := hvx1 x
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    exact_mod_cast h
  refine ⟨Matrix.posSemidef_sum _ fun x _ => (hpd x).smul (by
    exact_mod_cast (ENNReal.toReal_nonneg : 0 ≤ (S.law x).toReal)), ?_⟩
  simp only [PureSource.average, Matrix.trace_sum, Matrix.trace_smul, htr, smul_eq_mul, mul_one]
  exact_mod_cast hl

end X6CV

open X6CV

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X6CV

theorem rate_lower {a d : ℕ} (S : PureSource a d) : ∃ ε : ℝ → ℕ → ℝ,
    (∀ E, Tendsto (fun n : ℕ => ε E (n + 1)) atTop (nhds 0)) ∧
    ∀ (m : ℕ) (c : SourceCode S m) (lam E : ℝ), 0 ≤ E → 1 - c.fidelity ≤ lam →
      lam ≤ 1 - Real.exp (-E) → vnEntropy S.average - ε E m ≤ c.rate := by
  obtain ⟨sp, hsp⟩ := exists_res S.average (average_psd S).1 (average_psd S).2
  set H := vnEntropy S.average
  set N : ℝ := (spectralN sp : ℝ)
  set μ := spectralMu sp
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  -- μ = 0 forces N = 0
  have hμN : μ ≤ 0 → N = 0 := by
    intro hμ
    simp only [N, Nat.cast_eq_zero, spectralN, Finset.card_eq_zero]
    by_contra hne
    have hne' := Finset.nonempty_iff_ne_empty.mpr hne
    have : 0 < μ := by
      simp only [μ, spectralMu]
      rw [dif_pos hne']
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hne'
        (fun j => Real.sqrt ((sp.law j).toReal * (1 - (sp.law j).toReal)))
      rw [hjeq]; exact (Finset.mem_filter.mp hj).2
    linarith
  set μ' := if 0 < μ then μ else 1
  have hμ' : 0 < μ' := by simp only [μ']; split_ifs with h; exact h; norm_num
  set L0 := Real.log (8 * Real.sqrt N + 1)
  have hL0 : 0 ≤ L0 := Real.log_nonneg (by linarith [Real.sqrt_nonneg N])
  set α : ℝ → ℝ := fun E => Real.sqrt (E + L0 + 1) / μ'
  -- the tail term is at most e^{-Ep}/2
  have hterm : ∀ E, 0 ≤ E → 4 * Real.sqrt N * Real.exp (-μ ^ 2 * α E ^ 2) ≤ Real.exp (-E) / 2 := by
    intro E hE0
    by_cases hμ : 0 < μ
    · have hμμ : μ' = μ := by simp [μ', hμ]
      have e1 : μ ^ 2 * α E ^ 2 = E + L0 + 1 := by
        simp only [α, hμμ, div_pow, Real.sq_sqrt (by linarith [hE0] : 0 ≤ E + L0 + 1)]
        field_simp
      rw [neg_mul, e1, show -(E + L0 + 1) = -E + (-L0 + -1) by ring, Real.exp_add, Real.exp_add,
        Real.exp_neg L0, Real.exp_log (by positivity)]
      have h1 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
      have hs := Real.sqrt_nonneg N
      have hE := Real.exp_pos (-E)
      have h8 : 0 < 8 * Real.sqrt N + 1 := by positivity
      rw [show 4 * Real.sqrt N * (Real.exp (-E) * ((8 * Real.sqrt N + 1)⁻¹ * Real.exp (-1))) =
        Real.exp (-E) * Real.exp (-1) * (4 * Real.sqrt N / (8 * Real.sqrt N + 1)) by field_simp]
      have h2 : 4 * Real.sqrt N / (8 * Real.sqrt N + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ h8]; linarith
      calc Real.exp (-E) * Real.exp (-1) * (4 * Real.sqrt N / (8 * Real.sqrt N + 1))
          ≤ Real.exp (-E) * 1 * (1 / 2) := by
            gcongr
      _ = Real.exp (-E) / 2 := by ring
    · rw [hμN (not_lt.mp hμ)]; simp; positivity
  set K := varianceConstant * d
  set ε : ℝ → ℕ → ℝ := fun E m => E / Real.log 2 / (m : ℝ) + 1 / (m : ℝ) +
    K * (Real.sqrt ((E + L0 + 1) / (m : ℝ)) / μ')
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨ε, ?_, ?_⟩
  · intro E
    have hinv : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := hinv.const_mul (E / Real.log 2)
    have h2' := hinv.const_mul (E + L0 + 1)
    rw [mul_zero] at h2'
    have h2 := ((Real.continuous_sqrt.tendsto 0).comp h2').div_const μ'
    have h3 := (h1.add hinv).add (h2.const_mul K)
    simp only [mul_zero, Real.sqrt_zero, zero_div, add_zero] at h3
    refine h3.congr fun n => ?_
    simp only [ε, Function.comp_apply]
    push_cast
    ring_nf
  intro m c lam E hE0 hcode herror
  have hmpos := c.length_pos
  have hα : 0 < α E := div_pos (Real.sqrt_pos.mpr (by linarith)) hμ'
  have h19 := strongSourceConverse S sp hsp c lam (α E) hcode hα
  set mm : ℝ := (m : ℝ)
  have hm : 0 < mm := by simp only [mm]; exact_mod_cast hmpos
  set X := mm * H - K * α E * Real.sqrt mm
  have hB : Real.exp (-E) / 2 ≤ 1 - lam - 4 * Real.sqrt N * Real.exp (-μ ^ 2 * α E ^ 2) := by
    have := hterm E hE0
    linarith
  have hX : 0 < exp2 X := by simp only [exp2]; positivity
  have hdim : Real.exp (-E) / 2 * exp2 X ≤ c.dim := by
    refine le_trans ?_ (ge_iff_le.mp h19)
    exact mul_le_mul_of_nonneg_right hB hX.le
  have hlog : -E / Real.log 2 - 1 + X ≤ Real.logb 2 c.dim := by
    have hpos : 0 < Real.exp (-E) / 2 * exp2 X := by positivity
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hdim
    refine le_trans (le_of_eq ?_) this
    rw [Real.logb_mul (by positivity) hX.ne', Real.logb_div (by positivity) (by norm_num),
      Real.logb_self_eq_one (by norm_num)]
    simp only [exp2, Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
    rw [Real.logb, Real.log_exp]
  have hrate : c.rate = Real.logb 2 c.dim / mm := rfl
  rw [hrate, le_div_iff₀ hm]
  have hsm0 : 0 < Real.sqrt mm := Real.sqrt_pos.mpr hm
  have key : ∀ t : ℝ, 0 < t → ∀ A B x : ℝ,
      (A / t ^ 2 + B / t ^ 2 + K * (x / t / μ')) * t ^ 2 = A + B + K * (x / μ') * t := by
    intro t ht A B x; field_simp
  have hεm : ε E m * mm = E / Real.log 2 + 1 + K * α E * Real.sqrt mm := by
    calc ε E m * mm = (E / Real.log 2 / Real.sqrt mm ^ 2 + 1 / Real.sqrt mm ^ 2 +
          K * (Real.sqrt (E + L0 + 1) / Real.sqrt mm / μ')) * Real.sqrt mm ^ 2 := by
          simp only [ε]; rw [Real.sqrt_div' _ hm.le, Real.sq_sqrt hm.le]
      _ = _ := key _ hsm0 _ _ _
      _ = E / Real.log 2 + 1 + K * α E * Real.sqrt mm := by simp only [α]
  have : (H - ε E m) * mm = X - (E / Real.log 2 + 1) := by
    rw [sub_mul, hεm]; simp only [X]; ring
  rw [this]
  have : -E / Real.log 2 = -(E / Real.log 2) := by ring
  linarith

end X6CV


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X6SCODE

/-- a fixed tolerance `α` with `2·tail ≤ λ`. -/
lemma good_alpha {d : ℕ} (sp : FineResolution d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ α : ℝ, 0 < α ∧ 2 * varianceTail sp α ≤ lam := by
  set N : ℝ := (spectralN sp : ℝ)
  set μ := spectralMu sp
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hμN : μ ≤ 0 → N = 0 := by
    intro hμ
    simp only [N, Nat.cast_eq_zero, spectralN, Finset.card_eq_zero]
    by_contra hne
    have hne' := Finset.nonempty_iff_ne_empty.mpr hne
    have : 0 < μ := by
      simp only [μ, spectralMu]
      rw [dif_pos hne']
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hne'
        (fun j => Real.sqrt ((sp.law j).toReal * (1 - (sp.law j).toReal)))
      rw [hjeq]; exact (Finset.mem_filter.mp hj).2
    linarith
  by_cases hμ : 0 < μ
  · set L := Real.log (4 * N / lam + 1)
    have hL : 0 ≤ L := Real.log_nonneg (by
      have : 0 ≤ 4 * N / lam := by positivity
      linarith)
    refine ⟨Real.sqrt (L / 2 + 1) / μ, div_pos (Real.sqrt_pos.mpr (by linarith)) hμ, ?_⟩
    have e1 : spectralMu sp ^ 2 * (Real.sqrt (L / 2 + 1) / μ) ^ 2 = L / 2 + 1 := by
      rw [div_pow, Real.sq_sqrt (by linarith)]; simp only [μ]; field_simp
      exact div_self (ne_of_gt hμ)
    unfold varianceTail
    rw [show -2 * spectralMu sp ^ 2 * (Real.sqrt (L / 2 + 1) / μ) ^ 2 =
      -2 * (spectralMu sp ^ 2 * (Real.sqrt (L / 2 + 1) / μ) ^ 2) by ring, e1,
      show -2 * (L / 2 + 1) = -L + -2 by ring, Real.exp_add, Real.exp_neg, Real.exp_log (by positivity)]
    have h2 : Real.exp (-2) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    have hpos : 0 < 4 * N / lam + 1 := by positivity
    have : 2 * (2 * N * ((4 * N / lam + 1)⁻¹ * Real.exp (-2))) ≤ 2 * (2 * N * (4 * N / lam + 1)⁻¹) := by
      have := Real.exp_pos (-2)
      have : 0 ≤ 2 * N * (4 * N / lam + 1)⁻¹ := by positivity
      nlinarith
    refine this.trans ?_
    rw [show 2 * (2 * N * (4 * N / lam + 1)⁻¹) = 4 * N / (4 * N / lam + 1) by ring,
      div_le_iff₀ hpos]
    rw [mul_add, mul_div_cancel₀ _ hlam.ne']; linarith [hlam]
  · refine ⟨1, one_pos, ?_⟩
    unfold varianceTail
    have : (spectralN sp : ℝ) = 0 := hμN (not_lt.mp hμ)
    rw [this]; simp; exact hlam.le

end X6SCODE

open X6SCODE

theorem solution {a d : ℕ} (S : PureSource a d) (lambda : ℝ)
    (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    sourceRate S .quantumEntanglement lambda = ENNReal.ofReal (vnEntropy S.average) ∧
    sourceRate S .quantumFidelity lambda = ENNReal.ofReal (vnEntropy S.average) ∧
    sourceRate S .arbitraryFidelity lambda = ENNReal.ofReal (vnEntropy S.average) := by
  obtain ⟨sp, hsp⟩ := X6CV.exists_res S.average (X6CV.average_psd S).1 (X6CV.average_psd S).2
  obtain ⟨ε, hεt, hlow⟩ := X6CV.rate_lower S
  obtain ⟨α, hα, htail⟩ := good_alpha sp lambda hlambda
  set H := vnEntropy S.average
  set E0 := -Real.log (1 - lambda)
  have hE0 : 0 ≤ E0 := by
    simp only [E0]; rw [neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hE0' : lambda ≤ 1 - Real.exp (-E0) := by
    simp only [E0, neg_neg]; rw [Real.exp_log (by linarith)]; linarith
  -- generic lower bound
  have lower : ∀ q : SourceQuality,
      (∀ m (c : SourceCode S m), MeetsQuality c q lambda → 1 - c.fidelity ≤ lambda) →
      ENNReal.ofReal H ≤ sourceRate S q lambda := by
    intro q hq
    have hmin : ∀ n : ℕ, ENNReal.ofReal (H - ε E0 (n + 1)) ≤ minimumSourceRate S q (n + 1) lambda := by
      intro n; unfold minimumSourceRate
      refine le_sInf ?_
      rintro r ⟨c, hc, rfl⟩
      exact ENNReal.ofReal_le_ofReal (hlow (n + 1) c lambda E0 hE0 (hq _ c hc) hE0')
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (H - ε E0 (n + 1))) atTop
        (nhds (ENNReal.ofReal H)) := by
      have := (tendsto_const_nhds (x := H)).sub (hεt E0)
      simp only [sub_zero] at this
      exact ENNReal.tendsto_ofReal this
    unfold sourceRate
    calc ENNReal.ofReal H = liminf (fun n : ℕ => ENNReal.ofReal (H - ε E0 (n + 1))) atTop :=
          htend.liminf_eq.symm
      _ ≤ liminf (fun n : ℕ => minimumSourceRate S q (n + 1) lambda) atTop :=
          liminf_le_liminf (Eventually.of_forall hmin)
      _ ≤ _ := liminf_le_limsup
  -- generic upper bound
  have upper : ∀ q : SourceQuality,
      (∀ m (c : SourceCode S m) E, EncoderExtension c E →
        1 - sourceFe (copies m S.average) (c.decode ∘ E) ≤ lambda → MeetsQuality c q lambda) →
      sourceRate S q lambda ≤ ENNReal.ofReal H := by
    intro q hq
    have hmin : ∀ n : ℕ, minimumSourceRate S q (n + 1) lambda ≤
        ENNReal.ofReal (H + varianceConstant * d * α / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
      intro n
      have hne : 0 < (varianceSet sp.law (n + 1) α).card := by
        by_contra h0
        have hcard : varianceSet sp.law (n + 1) α = ∅ := Finset.card_eq_zero.mp (by omega)
        have VT := varianceTypical sp (n + 1) (by omega) α hα
        simp only at VT
        obtain ⟨-, hmass, -⟩ := VT
        have hz : varianceProjector sp (n + 1) α = 0 := by
          unfold varianceProjector; rw [hcard]; simp
        rw [hz] at hmass
        unfold effectProb at hmass
        simp at hmass
        linarith
      obtain ⟨c, E, hE, hfe, hrate⟩ := X6ACH.achieve S sp hsp (n + 1) (by omega) α hα hne
      have hq' := hq _ c E hE (by linarith)
      unfold minimumSourceRate
      have hmem : ENNReal.ofReal c.rate ∈ {r | ∃ c : SourceCode S (n + 1), MeetsQuality c q lambda ∧
          r = ENNReal.ofReal c.rate} := ⟨c, hq', rfl⟩
      exact (sInf_le hmem).trans (ENNReal.ofReal_le_ofReal hrate)
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (H + varianceConstant * d * α /
        Real.sqrt ((n + 1 : ℕ) : ℝ))) atTop (nhds (ENNReal.ofReal H)) := by
      have hinv : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := ((Real.continuous_sqrt.tendsto 0).comp hinv).const_mul (varianceConstant * d * α)
      simp only [Real.sqrt_zero, mul_zero] at h2
      have h3 := (tendsto_const_nhds (x := H)).add h2
      simp only [add_zero] at h3
      refine ENNReal.tendsto_ofReal (h3.congr fun n => ?_)
      simp only [Function.comp_apply, Real.sqrt_div' 1 (by positivity : (0 : ℝ) ≤ n + 1), Real.sqrt_one]
      push_cast; ring
    unfold sourceRate
    calc limsup (fun n : ℕ => minimumSourceRate S q (n + 1) lambda) atTop
        ≤ limsup (fun n : ℕ => ENNReal.ofReal (H + varianceConstant * d * α /
            Real.sqrt ((n + 1 : ℕ) : ℝ))) atTop := limsup_le_limsup (Eventually.of_forall hmin)
      _ = ENNReal.ofReal H := htend.limsup_eq
  have fe_le := fun m (c : SourceCode S m) E (hE : EncoderExtension c E) => X6SRC.code_fe_le S c E hE
  refine ⟨le_antisymm (upper _ ?_) (lower _ ?_), le_antisymm (upper _ ?_) (lower _ ?_),
    le_antisymm (upper _ ?_) (lower _ ?_)⟩
  · intro m c E hE h; exact ⟨E, hE, h⟩
  · intro m c h
    obtain ⟨E, hE, h⟩ := h
    linarith [fe_le m c E hE]
  · intro m c E hE h; exact ⟨⟨E, hE⟩, by linarith [fe_le m c E hE]⟩
  · intro m c h; exact h.2
  · intro m c E hE h; show 1 - c.fidelity ≤ lambda; linarith [fe_le m c E hE]
  · intro m c h; exact h

