-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.universalCompression
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:25:26.962246+00:00
-- url     : https://prove2.me/submissions/52d60e1f-1330-4307-8a99-9c780f097f2c

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


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Dependency50.P19 (count)

namespace X6UC

open X6TWL X6TER

variable {d n : ℕ}

lemma count_sum (w : Fin n → Fin d) : ∑ j, count w j = n := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin d))) (f := w) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

/-- the spectral resolution with the same basis as `F` and the empirical weights of `w`. -/
def tres (F : FineResolution d) (hn : 0 < n) (w : Fin n → Fin d) : FineResolution d where
  weight j := (count w j : ℝ) / n
  nonneg j := by positivity
  total := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← Finset.sum_div, div_eq_one_iff_eq hn']; exact_mod_cast count_sum w
  basis := F.basis

lemma vec_dot (F : FineResolution d) (w w' : Fin n → Fin d) :
    star (vec (fun _ => F) w) ⬝ᵥ vec (fun _ => F) w' = if w = w' then 1 else 0 := by
  simp only [vec, dotProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i j => star ((F.basis : Matrix (Fin d) (Fin d) ℂ) j (w i)) *
    (F.basis : Matrix (Fin d) (Fin d) ℂ) j (w' i))]
  have hU : ∀ x y, ∑ j, star ((F.basis : Matrix (Fin d) (Fin d) ℂ) j x) *
      (F.basis : Matrix (Fin d) (Fin d) ℂ) j y = if x = y then 1 else 0 := by
    intro x y
    have hUU := Matrix.mem_unitaryGroup_iff'.mp F.basis.2
    have := congrFun (congrFun hUU x) y
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at this
    exact this
  simp only [hU]
  by_cases h : w = w'
  · subst h; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma P_mulVec (F : FineResolution d) (w w' : Fin n → Fin d) :
    P (fun _ => F) w' *ᵥ vec (fun _ => F) w =
      if w' = w then vec (fun _ => F) w' else 0 := by
  have e : P (fun _ => F) w' = Matrix.vecMulVec (vec (fun _ => F) w') (star (vec (fun _ => F) w')) := by
    ext a b
    simp only [P, wordTensor, FineResolution.atom, vec, Matrix.vecMulVec_apply, Pi.star_apply,
      Finset.prod_mul_distrib, star_prod]
    rfl
  rw [e, Matrix.vecMulVec_mulVec, vec_dot]
  split_ifs <;> simp

lemma mem_set (F : FineResolution d) (hn : 0 < n) (w : Fin n → Fin d) :
    w ∈ varianceSet (tres F hn w).law n 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [varianceSet, Finset.mem_filter, Finset.mem_univ, true_and, law_eq]
  intro j
  simp only [tres, zero_mul]
  rw [mul_div_cancel₀ _ hn']; simp

lemma act_eq (F : FineResolution d) (hn : 0 < n) (w : Fin n → Fin d) :
    act (varianceProjector (tres F hn w) n 0) (WithLp.toLp 2 (vec (fun _ => F) w)) =
      WithLp.toLp 2 (vec (fun _ => F) w) := by
  unfold act varianceProjector
  congr 1
  simp only [WithLp.ofLp_toLp]
  rw [Matrix.sum_mulVec]
  have hP : ∀ w' : Fin n → Fin d, wordTensor (fun k => (tres F hn w).atom (w' k)) = P (fun _ => F) w' := fun _ => rfl
  simp only [hP, P_mulVec]
  rw [Finset.sum_ite_eq' (varianceSet (tres F hn w).law n 0) w, if_pos (mem_set F hn w)]

lemma mem_range (F : FineResolution d) (hn : 0 < n) (R : ℝ) (w : Fin n → Fin d)
    (h : vnEntropy (tres F hn w).state ≤ R) :
    WithLp.toLp 2 (vec (fun _ => F) w) ∈ universalRange d n R :=
  Submodule.subset_span ⟨tres F hn w, h, _, (act_eq F hn w).symm⟩

lemma proj_mulVec (R : ℝ) (x : EuclideanSpace ℂ (Fin n → Fin d)) (hx : x ∈ universalRange d n R) :
    universalProjector d n R *ᵥ WithLp.ofLp x = WithLp.ofLp x := by
  funext a
  set Q := (universalRange d n R).starProjection
  have hsum : x = ∑ b, (WithLp.ofLp x b) • ket b := by
    ext c; simp [ket, Pi.single_apply]
  have hPx : Q x = x := Submodule.starProjection_eq_self_iff.mpr hx
  calc (universalProjector d n R *ᵥ WithLp.ofLp x) a
      = ∑ b, inner ℂ (ket a) (Q (ket b)) * WithLp.ofLp x b := rfl
    _ = inner ℂ (ket a) (Q (∑ b, (WithLp.ofLp x b) • ket b)) := by
        rw [map_sum, inner_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_smul, inner_smul_right, mul_comm]
    _ = inner ℂ (ket a) x := by rw [← hsum, hPx]
    _ = WithLp.ofLp x a := by simp [ket, EuclideanSpace.inner_single_left]

lemma tr_lower (F : FineResolution d) (hn : 0 < n) (R : ℝ) {k : ℕ}
    (V : Matrix (Fin n → Fin d) (Fin k) ℂ) (hrange : V * Vᴴ = universalProjector d n R) :
    1 - ((QAlgorithms.Papers.Independent.Information100.P60.copies n F.state) * (V * Vᴴ)).trace.re ≤
      ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin d => R < vnEntropy (tres F hn w).state),
        ∏ i, F.weight (w i) := by
  set S : Fin n → FineResolution d := fun _ => F
  have hc : QAlgorithms.Papers.Independent.Information100.P60.copies n F.state =
      wordTensor (fun i => (S i).state) := rfl
  set g : (Fin n → Fin d) → ℝ := fun w => (star (vec S w) ⬝ᵥ ((V * Vᴴ) *ᵥ vec S w)).re
  have hg0 : ∀ w, 0 ≤ g w := by
    intro w
    have h := (Matrix.posSemidef_self_mul_conjTranspose V).dotProduct_mulVec_nonneg (vec S w)
    exact (Complex.nonneg_iff.mp h).1
  have hg1 : ∀ w, vnEntropy (tres F hn w).state ≤ R → g w = 1 := by
    intro w hw
    simp only [g]
    rw [hrange, proj_mulVec R _ (mem_range F hn R w hw)]
    simp only [WithLp.ofLp_toLp]
    rw [vec_dot, if_pos rfl]; simp
  have htr : ((QAlgorithms.Papers.Independent.Information100.P60.copies n F.state) *
      (V * Vᴴ)).trace.re = ∑ w, (∏ i, F.weight (w i)) * g w := by
    rw [hc, rho_eq, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, P_tr_mul, smul_eq_mul, Complex.re_ofReal_mul]
  have htot : ∑ w : Fin n → Fin d, ∏ i, F.weight (w i) = 1 :=
    X6TWL.total (fun _ j => F.weight j) (fun _ => F.total)
  rw [htr]
  set B := Finset.univ.filter (fun w : Fin n → Fin d => R < vnEntropy (tres F hn w).state)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w : Fin n → Fin d => R < vnEntropy (tres F hn w).state) (fun w => ∏ i, F.weight (w i))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w : Fin n → Fin d => R < vnEntropy (tres F hn w).state)
    (fun w => (∏ i, F.weight (w i)) * g w)
  have hW0 : ∀ w : Fin n → Fin d, 0 ≤ ∏ i, F.weight (w i) :=
    fun w => Finset.prod_nonneg fun i _ => F.nonneg _
  have hgood : ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin d => ¬ R < vnEntropy (tres F hn w).state),
      (∏ i, F.weight (w i)) * g w = ∑ w ∈ Finset.univ.filter
        (fun w : Fin n → Fin d => ¬ R < vnEntropy (tres F hn w).state), ∏ i, F.weight (w i) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hg1 w (not_lt.mp (Finset.mem_filter.mp hw).2), mul_one]
  have hbad : 0 ≤ ∑ w ∈ B, (∏ i, F.weight (w i)) * g w :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hW0 w) (hg0 w)
  rw [← hsplit2, hgood]
  rw [htot] at hsplit
  linarith

lemma prod_word (f : Fin d → ℝ) (w : Fin n → Fin d) : ∏ i, f (w i) = ∏ j, f j ^ count w j := by
  rw [← Finset.prod_fiberwise Finset.univ w (fun i => f (w i))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => f j) (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
    Finset.prod_const]
  rfl

/-- type class of `w0`. -/
def T (w0 : Fin n → Fin d) : Finset (Fin n → Fin d) :=
  Finset.univ.filter fun w => ∀ j, count w j = count w0 j

lemma pow_exp {x : ℝ} {c : ℕ} (h : c = 0 ∨ 0 < x) : x ^ c = Real.exp (c * Real.log x) := by
  rcases h with h | h
  · subst h; simp
  · rw [← Real.rpow_natCast, Real.rpow_def_of_pos h]; ring_nf

lemma mass (F : FineResolution d) (hn : 0 < n) (w0 : Fin n → Fin d) :
    ((T w0).card : ℝ) * ∏ j, ((tres F hn w0).weight j) ^ count w0 j ≤ 1 := by
  set q := (tres F hn w0).weight
  have hq0 : ∀ j, 0 ≤ q j := (tres F hn w0).nonneg
  calc ((T w0).card : ℝ) * ∏ j, q j ^ count w0 j
      = ∑ w ∈ T w0, ∏ i, q (w i) := by
        rw [Finset.sum_congr rfl (g := fun _ => ∏ j, q j ^ count w0 j) (fun w hw => by
          rw [prod_word]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [(Finset.mem_filter.mp hw).2 j])]
        simp
    _ ≤ ∑ w : Fin n → Fin d, ∏ i, q (w i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun w _ _ => Finset.prod_nonneg fun k _ => hq0 _)
    _ = 1 := X6TWL.total (fun _ => q) (fun _ => (tres F hn w0).total)

lemma fiber_eq (F : FineResolution d) (w0 : Fin n → Fin d) :
    ∑ w ∈ T w0, ∏ i, F.weight (w i) = ((T w0).card : ℝ) * ∏ j, F.weight j ^ count w0 j := by
  rw [Finset.sum_congr rfl (g := fun _ => ∏ j, F.weight j ^ count w0 j) (fun w hw => by
    rw [prod_word]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [(Finset.mem_filter.mp hw).2 j])]
  simp

/-- the classical divergence of the type of `w0` from the weights of `F` (natural log). -/
def K (F : FineResolution d) (hn : 0 < n) (w0 : Fin n → Fin d) : ℝ :=
  ∑ j, ((tres F hn w0).weight j * Real.log ((tres F hn w0).weight j) -
    (tres F hn w0).weight j * Real.log (F.weight j))

lemma fiber_le (F : FineResolution d) (hn : 0 < n) (w0 : Fin n → Fin d)
    (hsupp : ∀ j, 0 < count w0 j → 0 < F.weight j) :
    ∑ w ∈ T w0, ∏ i, F.weight (w i) ≤ Real.exp (-(n * K F hn w0)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set q := (tres F hn w0).weight
  have hqpos : ∀ j, 0 < count w0 j → 0 < q j := fun j hj => by
    show 0 < (count w0 j : ℝ) / n
    have : (0 : ℝ) < count w0 j := by exact_mod_cast hj
    positivity
  have hexp : ∀ f : Fin d → ℝ, (∀ j, 0 < count w0 j → 0 < f j) →
      ∏ j, f j ^ count w0 j = Real.exp (∑ j, (count w0 j : ℝ) * Real.log (f j)) := by
    intro f hf
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => pow_exp ?_
    rcases Nat.eq_zero_or_pos (count w0 j) with h | h
    · exact Or.inl h
    · exact Or.inr (hf j h)
  have hm := mass F hn w0
  rw [hexp q hqpos] at hm
  rw [fiber_eq, hexp F.weight hsupp]
  have hnK : -(n * K F hn w0) = ∑ j, (count w0 j : ℝ) * Real.log (F.weight j) +
      -∑ j, (count w0 j : ℝ) * Real.log (q j) := by
    simp only [K, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (n : ℝ) * q j = count w0 j := by
      show (n : ℝ) * ((count w0 j : ℝ) / n) = _
      field_simp
    rw [mul_sub, ← mul_assoc, ← mul_assoc, this]; ring
  rw [hnK, Real.exp_add, Real.exp_neg]
  set A := ∑ j, (count w0 j : ℝ) * Real.log (F.weight j)
  set B := ∑ j, (count w0 j : ℝ) * Real.log (q j)
  have hB := Real.exp_pos B
  have hc : ((T w0).card : ℝ) ≤ (Real.exp B)⁻¹ := by
    calc ((T w0).card : ℝ) = (T w0).card * Real.exp B * (Real.exp B)⁻¹ := by field_simp
      _ ≤ 1 * (Real.exp B)⁻¹ := mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr hB.le)
      _ = _ := one_mul _
  calc ((T w0).card : ℝ) * Real.exp A ≤ (Real.exp B)⁻¹ * Real.exp A :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := mul_comm _ _

lemma diag_herm (f : Fin d → ℝ) : IsSelfAdjoint (Matrix.diagonal (fun i => (f i : ℂ))) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma cfc_state (S : FineResolution d) (f : ℝ → ℝ) :
    cfc f S.state = (S.basis : Matrix (Fin d) (Fin d) ℂ) *
      Matrix.diagonal (fun j => ((f (S.weight j) : ℝ) : ℂ)) * (S.basis : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  set D := Matrix.diagonal (fun x => (S.weight x : ℂ))
  have hD : IsSelfAdjoint D := diag_herm _
  set φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) S.basis
  have hst : S.state = φ D := rfl
  have hφD : IsSelfAdjoint (φ D) := by
    rw [IsSelfAdjoint, ← map_star, hD.star_eq]
  have hcont : ContinuousOn f (spectrum ℝ D) :=
    ((Set.finite_range _).subset (X6TCR.spec_sub _)).continuousOn f
  rw [hst, ← StarAlgHomClass.map_cfc φ f D hcont (by
      show Continuous fun x : Matrix (Fin d) (Fin d) ℂ =>
        (S.basis : Matrix (Fin d) (Fin d) ℂ) * x * star (S.basis : Matrix (Fin d) (Fin d) ℂ)
      exact (continuous_const.mul continuous_id).mul continuous_const) hD hφD, X6TCR.cfc_diag]
  simp only [φ, Unitary.conjStarAlgAut_apply]
  rfl

lemma state_eq' (S : FineResolution d) :
    S.state = (S.basis : Matrix (Fin d) (Fin d) ℂ) *
      Matrix.diagonal (fun j => ((S.weight j : ℝ) : ℂ)) * (S.basis : Matrix (Fin d) (Fin d) ℂ)ᴴ := rfl

lemma UhU (S : FineResolution d) :
    (S.basis : Matrix (Fin d) (Fin d) ℂ)ᴴ * (S.basis : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem S.basis.2

lemma state_density (S : FineResolution d) : IsDensityMatrix S.state := by
  rw [state_eq']
  refine ⟨?_, ?_⟩
  · refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _
    refine Matrix.PosSemidef.diagonal fun j => ?_
    show (0 : ℂ) ≤ _
    exact_mod_cast S.nonneg j
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, UhU, Matrix.one_mul, Matrix.trace_diagonal]
    rw [← Complex.ofReal_sum, S.total]; simp

lemma ker_le (F : FineResolution d) (hn : 0 < n) (w0 : Fin n → Fin d)
    (hsupp : ∀ j, 0 < count w0 j → 0 < F.weight j) :
    LinearMap.ker F.state.mulVecLin ≤ LinearMap.ker (tres F hn w0).state.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
  set U := (F.basis : Matrix (Fin d) (Fin d) ℂ)
  have hb : (tres F hn w0).basis = F.basis := rfl
  rw [state_eq'] at hx ⊢
  rw [hb]
  set y := Uᴴ *ᵥ x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hx ⊢
  have hy : Matrix.diagonal (fun j => ((F.weight j : ℝ) : ℂ)) *ᵥ y = 0 := by
    have e : ∀ z, Uᴴ *ᵥ (U *ᵥ z) = z := fun z => by
      rw [Matrix.mulVec_mulVec, UhU, Matrix.one_mulVec]
    have := congrArg (fun z => Uᴴ *ᵥ z) hx
    simp only [Matrix.mulVec_zero] at this
    rwa [e] at this
  have hz : Matrix.diagonal (fun j => (((tres F hn w0).weight j : ℝ) : ℂ)) *ᵥ y = 0 := by
    funext j
    have := congrFun hy j
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at this ⊢
    rcases Nat.eq_zero_or_pos (count w0 j) with h | h
    · simp [tres, h]
    · have hl : ((F.weight j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hsupp j h).ne'
      rw [(mul_eq_zero.mp this).resolve_left hl, mul_zero]
  rw [hz, Matrix.mulVec_zero]

lemma tr_conj (U A : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) : (U * A * Uᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

lemma tr_conj2 (U A B : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    (U * A * Uᴴ * (U * B * Uᴴ)).trace = (A * B).trace := by
  have : U * A * Uᴴ * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  rw [this, tr_conj _ _ hU]

lemma umegaki_trace (F : FineResolution d) (hn : 0 < n) (w0 : Fin n → Fin d) :
    (cfc (fun x : ℝ => x * Real.log x) (tres F hn w0).state -
      (tres F hn w0).state * cfc Real.log F.state).trace.re = K F hn w0 := by
  have hb : ((tres F hn w0).basis : Matrix (Fin d) (Fin d) ℂ) = F.basis := rfl
  rw [cfc_state, cfc_state, state_eq' (tres F hn w0), hb, Matrix.trace_sub, tr_conj _ _ (UhU F),
    tr_conj2 _ _ _ (UhU F), Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Matrix.trace_diagonal,
    ← Finset.sum_sub_distrib, Complex.re_sum]
  unfold K
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]

lemma relBits_eq (F : FineResolution d) (hn : 0 < n) (w0 : Fin n → Fin d)
    (hsupp : ∀ j, 0 < count w0 j → 0 < F.weight j) :
    QAlgorithms.Papers.Independent.Information100.P60.relativeBits (tres F hn w0).state F.state =
      ENNReal.ofReal (K F hn w0 / Real.log 2) := by
  unfold QAlgorithms.Papers.Independent.Information100.P60.relativeBits
  rw [dif_pos ⟨state_density _, state_density _⟩]
  unfold QAlgorithms.QuantumLoss.umegakiEntropy
  rw [if_pos (ker_le F hn w0 hsupp), umegaki_trace,
    ENNReal.ofReal_div_of_pos (Real.log_pos one_lt_two)]

lemma tail_nonneg (D : ENNReal) : 0 ≤ divergenceTail n D := by
  unfold divergenceTail exp2; split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (by norm_num) _

lemma fiber_le_one (F : FineResolution d) (w0 : Fin n → Fin d) :
    ∑ w ∈ T w0, ∏ i, F.weight (w i) ≤ 1 := by
  calc _ ≤ ∑ w : Fin n → Fin d, ∏ i, F.weight (w i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun w _ _ => Finset.prod_nonneg fun k _ => F.nonneg _)
    _ = 1 := X6TWL.total (fun _ j => F.weight j) (fun _ => F.total)

lemma type_tail (F : FineResolution d) (hn : 0 < n) (R : ℝ) (w0 : Fin n → Fin d)
    (hbad : R < vnEntropy (tres F hn w0).state) :
    ∑ w ∈ T w0, ∏ i, F.weight (w i) ≤ divergenceTail n (highEntropyDivergence F.state R) := by
  set D := highEntropyDivergence F.state R
  by_cases hsupp : ∀ j, 0 < count w0 j → 0 < F.weight j
  · have hD : D ≤ ENNReal.ofReal (K F hn w0 / Real.log 2) :=
      sInf_le ⟨_, state_density _, hbad.le, (relBits_eq F hn w0 hsupp).symm⟩
    have hDt : D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
    have htoR : D.toReal ≤ max (K F hn w0 / Real.log 2) 0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
      rwa [ENNReal.toReal_ofReal'] at this
    unfold divergenceTail; rw [if_neg hDt]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmono : exp2 (-(n : ℝ) * max (K F hn w0 / Real.log 2) 0) ≤ exp2 (-(n : ℝ) * D.toReal) := by
      unfold exp2
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    refine le_trans ?_ hmono
    have hl2 := Real.log_pos one_lt_two
    rcases le_total 0 (K F hn w0 / Real.log 2) with hK | hK
    · rw [max_eq_left hK]
      refine (fiber_le F hn w0 hsupp).trans (le_of_eq ?_)
      unfold exp2
      rw [Real.rpow_def_of_pos two_pos]
      congr 1; field_simp
    · rw [max_eq_right hK, mul_zero]
      unfold exp2; rw [Real.rpow_zero]
      exact fiber_le_one F w0
  · push Not at hsupp
    obtain ⟨j, hj, hw⟩ := hsupp
    have hw0 : F.weight j = 0 := le_antisymm hw (F.nonneg j)
    rw [fiber_eq]
    have : ∏ j, F.weight j ^ count w0 j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hw0]; exact zero_pow hj.ne')
    rw [this, mul_zero]
    exact tail_nonneg _

lemma bad_sum (F : FineResolution d) (hn : 0 < n) (R : ℝ) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin d => R < vnEntropy (tres F hn w).state),
        ∏ i, F.weight (w i) ≤
      (n + 1 : ℝ) ^ d * divergenceTail n (highEntropyDivergence F.state R) := by
  set B := Finset.univ.filter (fun w : Fin n → Fin d => R < vnEntropy (tres F hn w).state)
  set τ : (Fin n → Fin d) → (Fin d → ℕ) := fun w j => count w j
  set tl := divergenceTail n (highEntropyDivergence F.state R)
  rw [← Finset.sum_fiberwise_of_maps_to (g := τ) (t := B.image τ)
    (fun w hw => Finset.mem_image_of_mem τ hw)]
  have hfib : ∀ c ∈ B.image τ, ∑ w ∈ B with τ w = c, ∏ i, F.weight (w i) ≤ tl := by
    intro c hc
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.mp hc
    refine le_trans ?_ (type_tail F hn R w0 (Finset.mem_filter.mp hw0).2)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun w _ _ => Finset.prod_nonneg fun k _ => F.nonneg _)
    intro w hw
    simp only [Finset.mem_filter] at hw
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun j => congrFun hw.2 j
  have himg : ((B.image τ).card : ℝ) ≤ (n + 1 : ℝ) ^ d := by
    have hsub : B.image τ ⊆ Fintype.piFinset (fun _ : Fin d => Finset.range (n + 1)) := by
      intro c hc
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hc
      rw [Fintype.mem_piFinset]; intro j
      rw [Finset.mem_range, Nat.lt_succ_iff, ← count_sum w]
      exact Finset.single_le_sum (f := fun j => count w j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have := Finset.card_le_card hsub
    rw [Fintype.card_piFinset] at this
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  calc _ ≤ ∑ c ∈ B.image τ, tl := Finset.sum_le_sum hfib
    _ = ((B.image τ).card : ℝ) * tl := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right himg (tail_nonneg _)

end X6UC

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open Filter

namespace X6UCS

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

end X6UCS

open X6UCS X6TSS X6UC
open QAlgorithms.Papers.Independent.Information100.P60 (copies)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {a d : ℕ} (S : PureSource a d)
    (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (V : Matrix (Fin n → Fin d) (Fin k) ℂ)
    (hisometry : Vᴴ * V = 1) (hrange : V * Vᴴ = universalProjector d n R) :
    sourceFe (copies n S.average) (conjSuperop V ∘ projectionEncoder V) ≥
      1 - 2 * (n+1 : ℝ)^d * divergenceTail n (highEntropyDivergence S.average R) := by
  obtain ⟨F, hF⟩ := exists_res S.average (average_psd S).1 (average_psd S).2
  rw [← hF]
  have hfid := fid_bound (copies n F.state) (copies_psd F n) k hk V hisometry
  have hlow := tr_lower F hn R V hrange
  have hbad := bad_sum F hn R
  set t := (copies n F.state * (V * Vᴴ)).trace.re
  set X := (n + 1 : ℝ) ^ d * divergenceTail n (highEntropyDivergence F.state R)
  rw [ge_iff_le]
  have : 1 - t ≤ X := hlow.trans hbad
  nlinarith [sq_nonneg (t - 1)]
