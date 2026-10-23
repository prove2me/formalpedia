-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.schumacherScheme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:06:55.595391+00:00
-- url     : https://prove2.me/submissions/16cdbbf6-283e-4402-97ae-337d76ff30ad

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

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

namespace X6TSS

variable {J : Type} [Fintype J] [DecidableEq J]

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

/-- the entanglement-fidelity identity for `X ↦ Π X Π + ((tr X - tr XΠ)/k) Π`. -/
lemma fid_identity (s Pi : Matrix J J ℂ) (hPi : Piᴴ = Pi) (k : ℂ) (T : Matrix J J ℂ → Matrix J J ℂ)
    (hT : ∀ X, T X = Pi * X * Pi + ((X.trace - (X * Pi).trace) / k) • Pi) :
    let ψ : J × J → ℂ := fun p => s p.2 p.1
    let Ψ : Matrix (J × J) (J × J) ℂ := fun a b => ψ a * conj (ψ b)
    (idTensorSuperop (R := J) T Ψ * Ψ).trace =
      (sᴴ * (Pi * s)).trace * conj ((sᴴ * (Pi * s)).trace) +
        (1 / k) * ((sᴴ * Pi * s) * (sᴴ * (1 - Pi) * s)).trace := by
  intro ψ Ψ
  set A := Pi * s
  have hPij : ∀ i j, Pi j i = conj (Pi i j) := by
    intro i j
    have := congrFun (congrFun hPi i) j
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]; simp
  -- entries of `id ⊗ T` applied to `Ψ`
  have hM : ∀ p q : J × J, idTensorSuperop (R := J) T Ψ p q =
      A p.2 p.1 * conj (A q.2 q.1) +
        ((sᴴ * (1 - Pi) * s) q.1 p.1 / k) * Pi p.2 q.2 := by
    intro p q
    simp only [idTensorSuperop, Matrix.of_apply]
    rw [hT]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1
    · simp only [A, Matrix.mul_apply, Matrix.of_apply, Ψ, ψ, Finset.sum_mul, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hPij q.2 a]; ring
    · congr 1
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Ψ, ψ,
        Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.one_apply, Finset.sum_mul,
        Finset.mul_sum, mul_sub, sub_mul, Finset.sum_sub_distrib]
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      congr 1
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.star_def]; ring
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.star_def]; ring
  set H := sᴴ * (1 - Pi) * s
  set G := sᴴ * Pi * s
  set z := (sᴴ * (Pi * s)).trace
  have hz : z = ∑ p : J × J, A p.2 p.1 * conj (ψ p) := by
    simp only [z, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, A, ψ,
      Matrix.conjTranspose_apply, Complex.star_def]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzc : conj z = ∑ q : J × J, conj (A q.2 q.1) * ψ q := by
    rw [hz, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  have hG : ∀ r r', G r r' = ∑ i, ∑ j, conj (s i r) * Pi i j * s j r' := by
    intro r r'
    simp only [G, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul]
    rw [Finset.sum_comm]
  calc (idTensorSuperop (R := J) T Ψ * Ψ).trace
      = ∑ p : J × J, ∑ q : J × J, idTensorSuperop (R := J) T Ψ p q * (ψ q * conj (ψ p)) := by
        simp only [Matrix.trace, Matrix.diag]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.mul_apply]
    _ = ∑ p : J × J, ∑ q : J × J, (A p.2 p.1 * conj (ψ p)) * (conj (A q.2 q.1) * ψ q) +
        ∑ p : J × J, ∑ q : J × J, (H q.1 p.1 / k) * Pi p.2 q.2 * ψ q * conj (ψ p) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hM]; ring
    _ = z * conj z + (1 / k) * (G * H).trace := by
        congr 1
        · rw [hzc, hz, Finset.sum_mul_sum]
        · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Fintype.sum_prod_type, ψ,
            Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r' _ => Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          ring


lemma fid_bound (ρ : Matrix J J ℂ) (hρ : ρ.PosSemidef) (k : ℕ) (hk : 0 < k)
    (V : Matrix J (Fin k) ℂ) (hiso : Vᴴ * V = 1) :
    ((ρ * (V * Vᴴ)).trace.re) ^ 2 ≤ sourceFe ρ (conjSuperop V ∘ projectionEncoder V) := by
  set Pi := V * Vᴴ
  have hPi : Piᴴ = Pi := by
    simp only [Pi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPP : Pi * Pi = Pi := by
    simp only [Pi]; rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hiso, Matrix.one_mul]
  have hT : ∀ X, (conjSuperop V ∘ projectionEncoder V) X =
      Pi * X * Pi + ((X.trace - (X * Pi).trace) / (k : ℂ)) • Pi := by
    intro X
    simp only [Function.comp_apply, conjSuperop, projectionEncoder, Pi]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
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
  have hid := fid_identity s Pi hPi (k : ℂ) _ hT
  unfold sourceFe effectProb
  have hpur : purification ρ = fun a b => s a.2 a.1 * conj (s b.2 b.1) := rfl
  rw [hpur, hid]
  set z := (sᴴ * (Pi * s)).trace
  have hz : z.re = (ρ * Pi).trace.re := by
    simp only [z]
    rw [hsh, Matrix.trace_mul_comm, Matrix.mul_assoc, hss, Matrix.trace_mul_comm]
  -- the second term is nonnegative
  have hPpsd : Pi.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have h1P : (1 - Pi).PosSemidef := by
    have e : 1 - Pi = (1 - Pi)ᴴ * (1 - Pi) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPi, Matrix.sub_mul, Matrix.one_mul,
        Matrix.mul_sub, Matrix.mul_one, hPP]; abel
    rw [e]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hG := hPpsd.conjTranspose_mul_mul_same s
  have hH := h1P.conjTranspose_mul_mul_same s
  have hGH := tr_nonneg hG hH
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Complex.add_re, show (1 / (k : ℂ)) = ((1 / (k : ℝ) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.mul_conj, Complex.ofReal_re]
  have hsq : z.re ^ 2 ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
  rw [← hz]
  have : 0 ≤ 1 / (k : ℝ) * ((sᴴ * Pi * s) * (sᴴ * (1 - Pi) * s)).trace.re :=
    mul_nonneg (by positivity) hGH
  linarith

end X6TSS

namespace X6TSS

open X6TWL X6TER

lemma P_psd' {d n : ℕ} (S : Fin n → FineResolution d) (w : Fin n → Fin d) : (P S w).PosSemidef := by
  have e : P S w = Matrix.vecMulVec (vec S w) (star (vec S w)) := by
    ext a b
    simp only [P, wordTensor, FineResolution.atom, vec, Matrix.vecMulVec_apply, Pi.star_apply,
      Finset.prod_mul_distrib, star_prod]
    rfl
  rw [e]; exact Matrix.posSemidef_vecMulVec_self_star _

lemma copies_psd {d : ℕ} (S : FineResolution d) (n : ℕ) :
    (QAlgorithms.Papers.Independent.Information100.P60.copies n S.state).PosSemidef := by
  have h : QAlgorithms.Papers.Independent.Information100.P60.copies n S.state =
      wordTensor (fun i => ((fun _ : Fin n => S) i).state) := rfl
  rw [h, rho_eq]
  refine Matrix.posSemidef_sum _ fun w _ => (P_psd' _ w).smul ?_
  rw [Complex.zero_le_real]
  exact Finset.prod_nonneg fun i _ => S.nonneg _

end X6TSS

open X6TSS
open QAlgorithms.Papers.Independent.Information100.P60 (copies)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {a d : ℕ} (S : PureSource a d) (spectral : FineResolution d)
    (haverage : spectral.state = S.average) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha : 0 < alpha) (k : ℕ) (hk : 0 < k)
    (V : Matrix (Fin n → Fin d) (Fin k) ℂ)
    (hisometry : Vᴴ * V = 1) (hrange : V * Vᴴ = varianceProjector spectral n alpha) :
    Real.logb 2 k / n ≤ vnEntropy S.average + varianceConstant * d * alpha / Real.sqrt n ∧
    sourceFe (copies n S.average) (conjSuperop V ∘ projectionEncoder V) ≥
      1 - 2 * varianceTail spectral alpha := by
  have hv := varianceTypical spectral n hn alpha halpha
  simp only at hv
  obtain ⟨_, h2, _, _, h5, _⟩ := hv
  rw [← haverage]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  constructor
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have htr : (k : ℝ) = (varianceProjector spectral n alpha).trace.re := by
      rw [← hrange, Matrix.trace_mul_comm, hisometry, Matrix.trace_one]; simp
    rw [← htr] at h5
    have hlog : Real.logb 2 k ≤ n * vnEntropy spectral.state +
        varianceConstant * d * alpha * Real.sqrt n := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) hk']; exact h5
    rw [div_le_iff₀ hn']
    have e : (vnEntropy spectral.state + varianceConstant * d * alpha / Real.sqrt n) * n =
        n * vnEntropy spectral.state + varianceConstant * d * alpha * Real.sqrt n := by
      field_simp
      have h := Real.mul_self_sqrt hn'.le
      linear_combination (-(varianceConstant * d * alpha)) * h
    rw [e]; exact hlog
  · have hF := fid_bound (copies n spectral.state) (copies_psd spectral n) k hk V hisometry
    rw [hrange] at hF
    have hp : effectProb (copies n spectral.state) (varianceProjector spectral n alpha) =
        (copies n spectral.state * varianceProjector spectral n alpha).trace.re := rfl
    rw [ge_iff_le, hp] at h2
    rw [ge_iff_le]
    set x := (copies n spectral.state * varianceProjector spectral n alpha).trace.re
    set t := varianceTail spectral alpha
    rcases le_or_gt 0 (1 - t) with h | h
    · have hx2 : (1 - t) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ h h2 2
      nlinarith [sq_nonneg t]
    · nlinarith [sq_nonneg x]
