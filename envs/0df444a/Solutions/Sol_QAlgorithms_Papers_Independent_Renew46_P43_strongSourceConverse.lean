-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.strongSourceConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:37:56.77427+00:00
-- url     : https://prove2.me/submissions/2bacd9fa-ff08-4b2d-8ed8-f099d6197956

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_varianceTypical

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

namespace X6SCL

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- squared Euclidean norm of a coordinate vector. -/
def nsq (f : ι → ℂ) : ℝ := ∑ i, ‖f i‖ ^ 2

lemma nsq_nonneg (f : ι → ℂ) : 0 ≤ nsq f := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma norm_toLp (f : ι → ℂ) : ‖(WithLp.toLp 2 f : EuclideanSpace ℂ ι)‖ = Real.sqrt (nsq f) := by
  rw [EuclideanSpace.norm_eq]; rfl

lemma sqrt_nsq_add (f g : ι → ℂ) : Real.sqrt (nsq (f + g)) ≤ Real.sqrt (nsq f) + Real.sqrt (nsq g) := by
  rw [← norm_toLp, ← norm_toLp, ← norm_toLp]
  have : (WithLp.toLp 2 (f + g) : EuclideanSpace ℂ ι) = WithLp.toLp 2 f + WithLp.toLp 2 g := rfl
  rw [this]; exact norm_add_le _ _

/-- Frobenius bound for the action of a matrix. -/
lemma frob (B : Matrix κ ι ℂ) (x : ι → ℂ) :
    nsq (B *ᵥ x) ≤ (∑ i, ∑ j, ‖B i j‖ ^ 2) * nsq x := by
  unfold nsq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(B *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖B i j‖ * ‖x j‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        simp only [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ (∑ j, ‖B i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma qf_ctc (B : Matrix κ ι ℂ) (x : ι → ℂ) :
    (star x ⬝ᵥ ((Bᴴ * B) *ᵥ x)).re = nsq (B *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  unfold nsq
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma trace_ctc (B : Matrix κ ι ℂ) : (Bᴴ * B).trace.re = ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable [DecidableEq ι]

lemma psd_ctc {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) : ∃ B : Matrix ι ι ℂ, σ = Bᴴ * B := by
  have hA0 : (0 : Matrix ι ι ℂ) ≤ σ := Matrix.nonneg_iff_posSemidef.mpr hσ
  have hs : (CFC.sqrt σ).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)
  refine ⟨CFC.sqrt σ, ?_⟩
  rw [hs.1.eq]; exact (CFC.sqrt_mul_sqrt_self σ hA0).symm

/-- a density matrix is below the identity. -/
lemma density_qf {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1) (x : ι → ℂ) :
    (star x ⬝ᵥ (σ *ᵥ x)).re ≤ nsq x := by
  obtain ⟨B, rfl⟩ := psd_ctc hσ
  rw [qf_ctc]
  have h1 : (Bᴴ * B).trace.re = 1 := by rw [htr]; simp
  rw [trace_ctc] at h1
  have := frob B x
  rw [h1, one_mul] at this; exact this

/-- the gentle estimate at vector level. -/
lemma gentle {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1) (v r : ι → ℂ)
    (hv : nsq v ≤ 1) :
    (star (v + r) ⬝ᵥ (σ *ᵥ (v + r))).re ≤
      (star v ⬝ᵥ (σ *ᵥ v)).re + 2 * Real.sqrt (nsq r) + nsq r := by
  obtain ⟨B, rfl⟩ := psd_ctc hσ
  have h1 : (Bᴴ * B).trace.re = 1 := by rw [htr]; simp
  rw [trace_ctc] at h1
  rw [qf_ctc, qf_ctc]
  have hBv : nsq (B *ᵥ v) ≤ 1 := by have := frob B v; rw [h1, one_mul] at this; linarith
  have hBr : nsq (B *ᵥ r) ≤ nsq r := by have := frob B r; rw [h1, one_mul] at this; exact this
  have tri := sqrt_nsq_add (B *ᵥ v) (B *ᵥ r)
  rw [← Matrix.mulVec_add] at tri
  set a := Real.sqrt (nsq (B *ᵥ v))
  set b := Real.sqrt (nsq (B *ᵥ r))
  have ha : a ^ 2 = nsq (B *ᵥ v) := Real.sq_sqrt (nsq_nonneg _)
  have hb : b ^ 2 = nsq (B *ᵥ r) := Real.sq_sqrt (nsq_nonneg _)
  have ha1 : a ≤ 1 := Real.sqrt_le_one.mpr hBv
  have hb1 : b ≤ Real.sqrt (nsq r) := Real.sqrt_le_sqrt hBr
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hc : nsq (B *ᵥ (v + r)) = Real.sqrt (nsq (B *ᵥ (v + r))) ^ 2 := (Real.sq_sqrt (nsq_nonneg _)).symm
  rw [hc]
  calc Real.sqrt (nsq (B *ᵥ (v + r))) ^ 2 ≤ (a + b) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) tri 2
    _ = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
    _ ≤ nsq (B *ᵥ v) + 2 * Real.sqrt (nsq r) + nsq r := by
        rw [ha]
        have : a * b ≤ Real.sqrt (nsq r) := by
          calc a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha1 hb0
            _ ≤ _ := by rw [one_mul]; exact hb1
        linarith

end X6SCL


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

namespace X6SC

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

end X6SC

namespace X6SC

open X6TWL X6TER X6SCL

variable {d : ℕ}

/-- projector facts for a sum of word projectors over a subset. -/
lemma proj_facts {n : ℕ} (S : Fin n → FineResolution d) (V : Finset (Fin n → Fin d)) :
    let Pr := ∑ w ∈ V, P S w
    Prᴴ = Pr ∧ Pr * Pr = Pr ∧ Pr.PosSemidef ∧ (1 - Pr).PosSemidef ∧ (1 - Pr)ᴴ = 1 - Pr ∧
      (1 - Pr) * (1 - Pr) = 1 - Pr := by
  intro Pr
  have hpsd : Pr.PosSemidef := Matrix.posSemidef_sum _ fun w _ => P_psd S w
  have hH : Prᴴ = Pr := hpsd.1.eq
  have hPP : Pr * Pr = Pr := by
    simp only [Pr, Finset.sum_mul, Finset.mul_sum, P_mul]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.sum_ite_eq']; simp [hu]
  have hQ : 1 - Pr = ∑ w ∈ Finset.univ.filter (fun w => w ∉ V), P S w := by
    have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ V) (P S)
    rw [sum_P] at this
    have hfV : Finset.univ.filter (fun w => w ∈ V) = V := by ext w; simp
    rw [hfV] at this
    rw [← this]; simp [Pr]
  have hQpsd : (1 - Pr).PosSemidef := by rw [hQ]; exact Matrix.posSemidef_sum _ fun w _ => P_psd S w
  refine ⟨hH, hPP, hpsd, hQpsd, hQpsd.1.eq, ?_⟩
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]; simp

end X6SC

namespace X6SC

open X6SCL

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma tr_rank1 (Y : Matrix ι ι ℂ) (u : ι → ℂ) :
    (Y * Matrix.of (fun a b => u a * conj (u b))).trace = star u ⬝ᵥ (Y *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]; ring

lemma conj_qf (M Pr : Matrix ι ι ℂ) (hH : Prᴴ = Pr) (u : ι → ℂ) :
    star (Pr *ᵥ u) ⬝ᵥ (M *ᵥ (Pr *ᵥ u)) = star u ⬝ᵥ ((Pr * M * Pr) *ᵥ u) := by
  rw [Matrix.star_mulVec, hH, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

lemma proj_qf (Pr : Matrix ι ι ℂ) (hH : Prᴴ = Pr) (hPP : Pr * Pr = Pr) (u : ι → ℂ) :
    (star u ⬝ᵥ (Pr *ᵥ u)).re = nsq (Pr *ᵥ u) := by
  rw [← qf_ctc, hH, hPP]

variable [DecidableEq ι]

lemma kraus_qf {m : ℕ} (R : Fin m → Matrix κ ι ℂ) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (v : κ → ℂ) :
    (star v ⬝ᵥ ((∑ k, R k * σ * (R k)ᴴ) *ᵥ v)).re ≤ (star v ⬝ᵥ ((∑ k, R k * (R k)ᴴ) *ᵥ v)).re := by
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have e1 : star v ⬝ᵥ ((R k * σ * (R k)ᴴ) *ᵥ v) = star ((R k)ᴴ *ᵥ v) ⬝ᵥ (σ *ᵥ ((R k)ᴴ *ᵥ v)) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e2 : (star v ⬝ᵥ ((R k * (R k)ᴴ) *ᵥ v)).re = nsq ((R k)ᴴ *ᵥ v) := by
    rw [← qf_ctc, Matrix.conjTranspose_conjTranspose]
  rw [e1, e2]
  exact density_qf hσ htr _

end X6SC

namespace X6SC

open scoped MatrixOrder

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma tr_nonneg {A B : Matrix J J ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  have hA0 : (0 : Matrix J J ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hs : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have e : A = CFC.sqrt A * CFC.sqrt A := (CFC.sqrt_mul_sqrt_self A hA0).symm
  rw [e, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have := (hB.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg
  rw [hs.1.eq] at this
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp this).1

end X6SC

open X6TWL X6TER X6SCL X6SC
open QAlgorithms.Papers.Independent.Information100.P06 (Below)
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {a d n : ℕ} (S : PureSource a d) (spectral : FineResolution d)
    (haverage : spectral.state = S.average) (c : SourceCode S n)
    (lambda alpha : ℝ) (hcode : 1 - c.fidelity ≤ lambda) (halpha : 0 < alpha) :
    (c.dim : ℝ) ≥
      (1 - lambda - 4 * Real.sqrt (spectralN spectral) *
        Real.exp (-(spectralMu spectral)^2 * alpha^2)) *
      exp2 (n * vnEntropy S.average - varianceConstant * d * alpha * Real.sqrt n) := by
  have hn := c.length_pos
  have VT := varianceTypical spectral n hn alpha halpha
  simp only at VT
  obtain ⟨-, hmass, -, hup, -, -⟩ := VT
  rw [haverage] at hmass hup
  set Pr := varianceProjector spectral n alpha with hPr
  set corr := varianceConstant * d * alpha * Real.sqrt n
  set kc := exp2 (-n * vnEntropy S.average + corr)
  set ρn := copies n S.average
  have hf := proj_facts (fun _ : Fin n => spectral) (varianceSet spectral.law n alpha)
  simp only at hf
  have hPrS : (∑ w ∈ varianceSet spectral.law n alpha, P (fun _ : Fin n => spectral) w) = Pr := rfl
  rw [hPrS] at hf
  obtain ⟨hH, hPP, hPpsd, hQpsd, hQH, hQQ⟩ := hf
  -- Kraus decoder
  obtain ⟨m, R, hR, hD⟩ := c.decoder_channel
  set G : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := ∑ k, R k * (R k)ᴴ
  have hG : G.PosSemidef := Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_self_mul_conjTranspose _
  have htrG : G.trace.re = c.dim := by
    simp only [G, Matrix.trace_sum]
    simp only [Matrix.trace_mul_comm (R _)]
    rw [← Matrix.trace_sum]
    have : (∑ k, (R k)ᴴ * R k) = 1 := hR
    rw [this, Matrix.trace_one]; simp
  -- letters and words
  choose vx hvx1 hvx using S.pure
  set u : (Fin n → Fin a) → (Fin n → Fin d) → ℂ := fun w b => ∏ i, vx (w i) (b i)
  have hword : ∀ w, S.word w = Matrix.of (fun x y => u w x * conj (u w y)) := by
    intro w; ext x y
    simp only [PureSource.word, wordTensor, hvx, pureDensity, u, Matrix.of_apply, map_prod,
      Finset.prod_mul_distrib]
  have hv1 : ∀ x, ∑ j, ‖vx x j‖ ^ 2 = 1 := by
    intro x
    have h := hvx1 x
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    exact h
  have hu1 : ∀ w, nsq (u w) = 1 := by
    intro w
    simp only [nsq, u, norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun i j => ‖vx (w i) j‖ ^ 2)]
    simp [hv1]
  -- weights
  set q : (Fin n → Fin a) → ℝ := fun w => S.weight w
  have hl : ∑ x, (S.law x).toReal = 1 := by
    have h := S.law.tsum_coe
    rw [tsum_fintype] at h
    rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ _), h]; simp
  have hq0 : ∀ w, 0 ≤ q w := fun w => Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hq1 : ∑ w, q w = 1 := X6TWL.total (fun _ x => (S.law x).toReal) (fun _ => hl)
  have hρn : ρn = ∑ w, ((q w : ℝ) : ℂ) • S.word w := by
    ext x y
    simp only [ρn, copies, PureSource.average, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [q, PureSource.weight, PureSource.word, wordTensor, Finset.prod_mul_distrib]
    push_cast; rfl
  -- decoded states
  set Y : (Fin n → Fin a) → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := fun w => c.decode (c.encode w)
  have hYk : ∀ w, Y w = ∑ k, R k * c.encode w * (R k)ᴴ := fun w => by simp only [Y, hD, krausApply]
  have hYpsd : ∀ w, (Y w).PosSemidef := fun w => by
    rw [hYk]; exact Matrix.posSemidef_sum _ fun k _ => (c.encoded_state w).1.mul_mul_conjTranspose_same _
  have hYtr : ∀ w, (Y w).trace = 1 := fun w => by
    rw [hYk, Matrix.trace_sum]
    simp only [Matrix.trace_mul_comm _ (R _)ᴴ, ← Matrix.mul_assoc]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hR, Matrix.one_mul]; exact (c.encoded_state w).2
  -- quadratic forms
  have hnq : ∀ x : (Fin n → Fin d) → ℂ, (star x ⬝ᵥ x).re = nsq x := fun x => by
    have := qf_ctc (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) x
    simpa using this
  set t : (Fin n → Fin a) → ℝ := fun w => nsq ((1 - Pr) *ᵥ u w)
  have ht0 : ∀ w, 0 ≤ t w := fun w => nsq_nonneg _
  have htw : ∀ w, t w = 1 - (Pr * S.word w).trace.re := fun w => by
    simp only [t]
    rw [← proj_qf _ hQH hQQ, hword, tr_rank1, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
      Matrix.one_mulVec, hnq, hu1]
  have hper : ∀ w, effectProb (Y w) (S.word w) ≤
      ((Pr * G * Pr) * S.word w).trace.re + 2 * Real.sqrt (t w) + t w := by
    intro w
    unfold effectProb
    rw [hword, tr_rank1, tr_rank1]
    have hsplit : u w = Pr *ᵥ u w + (1 - Pr) *ᵥ u w := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    have hv : nsq (Pr *ᵥ u w) ≤ 1 := by
      have h1 := proj_qf _ hH hPP (u w)
      have h2 := proj_qf _ hQH hQQ (u w)
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.one_mulVec, hnq, hu1] at h2
      linarith [nsq_nonneg (u w - Pr *ᵥ u w)]
    have g := gentle (hYpsd w) (hYtr w) (Pr *ᵥ u w) ((1 - Pr) *ᵥ u w) hv
    rw [← hsplit] at g
    refine g.trans ?_
    have k := kraus_qf R (c.encoded_state w).1 (c.encoded_state w).2 (Pr *ᵥ u w)
    rw [← hYk] at k
    rw [conj_qf (∑ k, R k * (R k)ᴴ) Pr hH] at k
    simp only [t]; linarith
  have hle1 : ∀ w, effectProb (Y w) (S.word w) ≤ 1 := by
    intro w; unfold effectProb; rw [hword, tr_rank1]
    have := density_qf (hYpsd w) (hYtr w) (u w)
    rw [hu1] at this; exact this
  -- summation
  have hF : c.fidelity = ∑ w, q w * effectProb (Y w) (S.word w) := rfl
  have lin : ∀ M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ,
      ∑ w, q w * (M * S.word w).trace.re = (M * ρn).trace.re := by
    intro M
    rw [hρn, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hkc : 0 < kc := by simp only [kc, exp2]; positivity
  have hA : ∑ w, q w * ((Pr * G * Pr) * S.word w).trace.re ≤ kc * c.dim := by
    rw [lin]
    have e1 : (Pr * G * Pr * ρn).trace = (G * (Pr * ρn * Pr)).trace := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, Matrix.mul_assoc G]
    rw [e1]
    have h1 := tr_nonneg hG hup
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.re_ofReal_mul] at h1
    have h2 := tr_nonneg hG hQpsd
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_one, htrG] at h2
    nlinarith
  set T := ∑ w, q w * t w
  have hT : T ≤ varianceTail spectral alpha := by
    have : T = 1 - (Pr * ρn).trace.re := by
      simp only [T, htw, mul_sub, mul_one, Finset.sum_sub_distrib, hq1, lin]
    rw [this]
    unfold effectProb at hmass
    rw [Matrix.trace_mul_comm] at hmass
    linarith
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun w _ => mul_nonneg (hq0 w) (ht0 w)
  have hs : ∑ w, q w * Real.sqrt (t w) ≤ Real.sqrt T := by
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => Real.sqrt (q w))
      (fun w => Real.sqrt (q w) * Real.sqrt (t w))
    have e1 : ∀ w, Real.sqrt (q w) * (Real.sqrt (q w) * Real.sqrt (t w)) = q w * Real.sqrt (t w) := by
      intro w; rw [← mul_assoc, Real.mul_self_sqrt (hq0 w)]
    have e2 : ∀ w, Real.sqrt (q w) ^ 2 = q w := fun w => Real.sq_sqrt (hq0 w)
    have e3 : ∀ w, (Real.sqrt (q w) * Real.sqrt (t w)) ^ 2 = q w * t w := by
      intro w; rw [mul_pow, Real.sq_sqrt (hq0 w), Real.sq_sqrt (ht0 w)]
    simp only [e1, e2, e3, hq1, one_mul] at cs
    exact Real.le_sqrt_of_sq_le cs
  have hFup : c.fidelity ≤ kc * c.dim + 2 * Real.sqrt T + T := by
    rw [hF]
    calc ∑ w, q w * effectProb (Y w) (S.word w)
        ≤ ∑ w, q w * (((Pr * G * Pr) * S.word w).trace.re + 2 * Real.sqrt (t w) + t w) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hper w) (hq0 w)
      _ = ∑ w, q w * ((Pr * G * Pr) * S.word w).trace.re + 2 * ∑ w, q w * Real.sqrt (t w) + T := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, T]
          congr 1; congr 1
          exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ _ := by linarith
  have hF1 : c.fidelity ≤ 1 := by
    rw [hF]
    calc ∑ w, q w * effectProb (Y w) (S.word w) ≤ ∑ w, q w * 1 :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hle1 w) (hq0 w)
      _ = 1 := by simp [hq1]
  -- final arithmetic
  set E := Real.exp (-(spectralMu spectral) ^ 2 * alpha ^ 2)
  set M := Real.sqrt (spectralN spectral) * E
  have hM0 : 0 ≤ M := by positivity
  have htail : varianceTail spectral alpha = 2 * M ^ 2 := by
    simp only [varianceTail, M, E, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * (-spectralMu spectral ^ 2 * alpha ^ 2) =
      -2 * spectralMu spectral ^ 2 * alpha ^ 2 by push_cast; ring]
    ring
  have key : 1 - lambda - 4 * M ≤ kc * c.dim := by
    rcases le_or_gt 1 (4 * M) with h | h
    · have : 0 ≤ kc * c.dim := by positivity
      linarith
    · set r := Real.sqrt T
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hr2 : r ^ 2 = T := Real.sq_sqrt hT0
      have hr : r ≤ 3 / 2 * M := by nlinarith
      have : 2 * r + T ≤ 4 * M := by nlinarith
      linarith
  have hexp : exp2 (n * vnEntropy S.average - corr) * kc = 1 := by
    simp only [kc, exp2]
    rw [← Real.rpow_add (by norm_num)]
    ring_nf; simp
  have hpos : 0 < exp2 (n * vnEntropy S.average - corr) := by simp only [exp2]; positivity
  rw [ge_iff_le]
  calc (1 - lambda - 4 * Real.sqrt (spectralN spectral) * E) * exp2 (n * vnEntropy S.average - corr)
      ≤ (kc * c.dim) * exp2 (n * vnEntropy S.average - corr) := by
        refine mul_le_mul_of_nonneg_right ?_ hpos.le
        simp only [M] at key; linarith
    _ = c.dim := by rw [mul_comm kc, mul_assoc, mul_comm kc, hexp, mul_one]

