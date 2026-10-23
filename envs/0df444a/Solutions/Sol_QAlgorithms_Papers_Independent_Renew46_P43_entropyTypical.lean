-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.entropyTypical
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:21:14.654308+00:00
-- url     : https://prove2.me/submissions/a194036f-8e98-4651-a909-f860658db2a1

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

open scoped BigOperators

namespace X6ETV

/-- `h(x) = e^x (x² - 2Lx + 2L)`. -/
def h (L x : ℝ) : ℝ := Real.exp x * (x ^ 2 - 2 * L * x + 2 * L)

lemma h_deriv (L x : ℝ) : HasDerivAt (h L) (Real.exp x * x * (x - (2 * L - 2))) x := by
  have h1 : HasDerivAt (fun y => Real.exp y) (Real.exp x) x := Real.hasDerivAt_exp x
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 - 2 * L * y + 2 * L) (2 * x - 2 * L) x := by
    exact (((hasDerivAt_pow 2 x).sub ((hasDerivAt_id' x).const_mul (2 * L))).add_const
      (2 * L)).congr_deriv (by norm_num)
  have := h1.mul h2
  unfold h
  exact this.congr_deriv (by ring)

lemma h_cont (L : ℝ) : Continuous (h L) := by unfold h; fun_prop

lemma h_le_neg (L x : ℝ) (hL : 1 ≤ L) (hx : x ≤ 0) : h L x ≤ 2 * L := by
  unfold h
  have hy := Real.quadratic_le_exp_of_nonneg (show 0 ≤ -x by linarith)
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos x
  -- x² - 2Lx + 2L ≤ 2L e^{-x}
  have key : x ^ 2 - 2 * L * x + 2 * L ≤ 2 * L * Real.exp (-x) := by
    nlinarith [sq_nonneg x]
  calc Real.exp x * (x ^ 2 - 2 * L * x + 2 * L) ≤ Real.exp x * (2 * L * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left key hpos.le
    _ = 2 * L := by rw [mul_comm, mul_assoc, mul_comm (Real.exp (-x)), he, mul_one]

lemma h_anti (L : ℝ) (hL : 1 ≤ L) : AntitoneOn (h L) (Set.Icc 0 (2 * L - 2)) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (h_cont L).continuousOn
    (fun x _ => (h_deriv L x).hasDerivWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  have := Real.exp_pos x
  have : 0 ≤ Real.exp x * x := by nlinarith [hx.1]
  nlinarith [hx.2]

lemma h_mono (L : ℝ) (hL : 1 ≤ L) : MonotoneOn (h L) (Set.Ici (2 * L - 2)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) (h_cont L).continuousOn
    (fun x _ => (h_deriv L x).hasDerivWithinAt) ?_
  intro x hx
  rw [interior_Ici] at hx
  have := Real.exp_pos x
  have hx' : (2 * L - 2) < x := hx
  have : 0 ≤ Real.exp x * x := by nlinarith
  nlinarith

lemma exp_le_of_pow {a : ℝ} {k : ℕ} (hk : k ≠ 0) (y : ℝ) (h : Real.exp (k * a) ≤ y ^ k) (hy : 0 ≤ y) :
    Real.exp a ≤ y := by
  rw [Real.exp_nat_mul] at h  -- exp (k*a) = exp a ^ k
  exact (pow_le_pow_iff_left₀ (Real.exp_pos a).le hy hk).mp h

lemma exp_one_pow_lt (k : ℕ) : Real.exp 1 ^ k ≤ (2.7182818286 : ℝ) ^ k :=
  pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le k

/-- `ln d ≥ 2 - 2/d` for `d ∈ {5,6,7}` in the form `d (2 - L) ≤ 2`. -/
lemma small_d (d : ℕ) (h5 : 5 ≤ d) (h7 : d ≤ 7) : (d : ℝ) * (2 - Real.log d) ≤ 2 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  suffices Real.exp (2 - 2 / d) ≤ d by
    have := Real.log_le_log (Real.exp_pos _) this
    rw [Real.log_exp] at this
    have : 2 - Real.log d ≤ 2 / d := by linarith
    calc (d : ℝ) * (2 - Real.log d) ≤ d * (2 / d) := mul_le_mul_of_nonneg_left this hd.le
      _ = 2 := by field_simp
  interval_cases d
  · refine exp_le_of_pow (k := 5) (by norm_num) _ ?_ (by norm_num)
    rw [show ((5 : ℕ) : ℝ) * (2 - 2 / ((5 : ℕ) : ℝ)) = (8 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (exp_one_pow_lt 8).trans (by norm_num)
  · refine exp_le_of_pow (k := 3) (by norm_num) _ ?_ (by norm_num)
    rw [show ((3 : ℕ) : ℝ) * (2 - 2 / ((6 : ℕ) : ℝ)) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (exp_one_pow_lt 5).trans (by norm_num)
  · refine exp_le_of_pow (k := 7) (by norm_num) _ ?_ (by norm_num)
    rw [show ((7 : ℕ) : ℝ) * (2 - 2 / ((7 : ℕ) : ℝ)) = (12 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (exp_one_pow_lt 12).trans (by norm_num)

lemma two_le_log (d : ℕ) (h8 : 8 ≤ d) : 2 ≤ Real.log d := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have : Real.exp 2 ≤ 8 := by
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (exp_one_pow_lt 2).trans (by norm_num)
  exact this.trans (by exact_mod_cast h8)

lemma log5 (d : ℕ) (h5 : 5 ≤ d) : 1 ≤ Real.log d := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have : Real.exp 1 ≤ 5 := Real.exp_one_lt_d9.le.trans (by norm_num)
  exact this.trans (by exact_mod_cast h5)

/-- the tangent-line bound for `d ≥ 5`. -/
lemma tangent (d : ℕ) (h5 : 5 ≤ d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * Real.log p ^ 2 ≤ 2 * Real.log d / d + (Real.log d ^ 2 - 2 * Real.log d) * p := by
  set L := Real.log d
  have hd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hL1 : 1 ≤ L := log5 d h5
  rcases hp0.eq_or_lt with h0 | hp
  · subst h0; simp; positivity
  set x := Real.log p + L
  have hxL : x ≤ L := by simp only [x]; linarith [Real.log_nonpos hp0 hp1]
  have hex : Real.exp x = p * d := by
    simp only [x, L]; rw [Real.exp_add, Real.exp_log hp, Real.exp_log hd]
  have hhx : h L x ≤ 2 * L := by
    rcases le_total x 0 with hx0 | hx0
    · exact h_le_neg L x hL1 hx0
    · rcases le_total x (2 * L - 2) with hx2 | hx2
      · have := h_anti L hL1 ⟨le_refl 0, by linarith⟩ ⟨hx0, hx2⟩ hx0
        refine this.trans (le_of_eq ?_); simp [h]
      · have := h_mono L hL1 hx2 (show 2 * L - 2 ≤ L by linarith) hxL
        refine this.trans ?_
        have hLt : L < 2 ∨ 2 ≤ L := lt_or_ge L 2
        rcases hLt with hLt | hLt
        · have h7 : d ≤ 7 := by
            by_contra hc; push Not at hc
            linarith [two_le_log d hc]
          have hs := small_d d h5 h7
          simp only [h]
          rw [Real.exp_log hd]
          have : L ^ 2 - 2 * L * L + 2 * L = L * (2 - L) := by ring
          rw [this]
          nlinarith
        · have : h L L ≤ h L 0 :=
            h_anti L hL1 ⟨le_refl 0, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
          refine this.trans (le_of_eq ?_); simp [h]
  -- translate
  have hlp : Real.log p = x - L := by simp only [x]; ring
  rw [hlp]
  have hpd : p = Real.exp x / d := by rw [hex]; field_simp
  rw [hpd]
  have key : Real.exp x * (x - L) ^ 2 ≤ 2 * L + (L ^ 2 - 2 * L) * Real.exp x := by
    have : Real.exp x * (x - L) ^ 2 = h L x + (L ^ 2 - 2 * L) * Real.exp x := by simp only [h]; ring
    linarith
  have e1 : Real.exp x / d * (x - L) ^ 2 = (Real.exp x * (x - L) ^ 2) / d := by ring
  have e2 : 2 * L / d + (L ^ 2 - 2 * L) * (Real.exp x / d) =
      (2 * L + (L ^ 2 - 2 * L) * Real.exp x) / d := by ring
  rw [e1, e2]; exact div_le_div_of_nonneg_right key hd.le

lemma poly (y : ℝ) (hy : 0 ≤ y) :
    (1 / 2 - y) ^ 2 + 3 / 20 ≤ 41 / 100 * (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24) := by
  nlinarith [sq_nonneg (y - 1), sq_nonneg (y - 2), sq_nonneg (y ^ 2 - 2 * y), mul_nonneg hy (sq_nonneg (y - 1)),
    mul_nonneg hy (sq_nonneg (y - 2)), sq_nonneg (y ^ 2 - 3 * y + 1)]

lemma cert (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (Real.log p + 1 / 2) ^ 2 ≤ 41 / 100 + (-3 / 20) * p := by
  rcases hp0.eq_or_lt with h0 | hp
  · subst h0; norm_num
  set y := -Real.log p
  have hy : 0 ≤ y := by simp only [y]; linarith [Real.log_nonpos hp0 hp1]
  have hT := Real.sum_le_exp_of_nonneg hy 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hP := poly y hy
  have hpe : p * Real.exp y = 1 := by
    simp only [y]; rw [Real.exp_neg, Real.exp_log hp]; field_simp
  have hlog : Real.log p + 1 / 2 = 1 / 2 - y := by simp only [y]; ring
  rw [hlog]
  -- (1/2 - y)^2 + 3/20 ≤ 41/100 e^y, multiply by p
  have h1 : (1 / 2 - y) ^ 2 + 3 / 20 ≤ 41 / 100 * Real.exp y := by nlinarith
  have := mul_le_mul_of_nonneg_left h1 hp.le
  nlinarith

lemma log3 : (1.05 : ℝ) ≤ Real.log 3 := by
  have h2 := Real.log_two_gt_d9
  have h43 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have e : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e]; norm_num at h43 ⊢; linarith

lemma log4 : (1.38 : ℝ) ≤ Real.log 4 := by
  have h2 := Real.log_two_gt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith

/-- the per-letter variance bound (natural logarithms). -/
lemma var_bound (d : ℕ) (hd : 0 < d) (p : Fin d → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) :
    ∑ j, p j * (Real.log (p j) + -∑ i, p i * Real.log (p i)) ^ 2 ≤
      max (Real.log 3 ^ 2) (Real.log d ^ 2) := by
  set H := -∑ i, p i * Real.log (p i)
  have hp1 : ∀ j, p j ≤ 1 := fun j => by
    rw [← hp]; exact Finset.single_le_sum (fun i _ => hp0 i) (Finset.mem_univ j)
  have shift : ∀ c : ℝ, ∑ j, p j * (Real.log (p j) + H) ^ 2 ≤ ∑ j, p j * (Real.log (p j) + c) ^ 2 := by
    intro c
    have e : ∀ j, p j * (Real.log (p j) + c) ^ 2 = p j * (Real.log (p j) + H) ^ 2 +
        2 * (c - H) * (p j * Real.log (p j)) + (2 * (c - H) * H + (c - H) ^ 2) * p j := by
      intro j; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hp]
    have : ∑ j, p j * Real.log (p j) = -H := by simp [H]
    rw [this]; nlinarith [sq_nonneg (c - H)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases h5 : 5 ≤ d
  · refine (shift 0).trans (le_trans ?_ (le_max_right _ _))
    simp only [add_zero]
    calc ∑ j, p j * Real.log (p j) ^ 2 ≤ ∑ j, (2 * Real.log d / d + (Real.log d ^ 2 - 2 * Real.log d) * p j) :=
          Finset.sum_le_sum fun j _ => tangent d h5 (p j) (hp0 j) (hp1 j)
      _ = Real.log d ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp; ring
  · refine (shift (1 / 2)).trans ?_
    have hs : ∑ j, p j * (Real.log (p j) + 1 / 2) ^ 2 ≤ (d : ℝ) * (41 / 100) + (-3 / 20) := by
      calc ∑ j, p j * (Real.log (p j) + 1 / 2) ^ 2 ≤ ∑ j, (41 / 100 + (-3 / 20) * p j) :=
            Finset.sum_le_sum fun j _ => cert (p j) (hp0 j) (hp1 j)
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]; ring
    refine hs.trans ?_
    by_cases h4 : d = 4
    · subst h4
      refine le_trans ?_ (le_max_right _ _)
      have := log4; nlinarith
    · have : (d : ℝ) ≤ 3 := by exact_mod_cast (by omega : d ≤ 3)
      refine le_trans ?_ (le_max_left _ _)
      have := log3; nlinarith

end X6ETV


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

namespace X6ETM

open X6TWL

variable {I : Type} [Fintype I] [DecidableEq I]

/-- variance of a sum of independent centred letters. -/
lemma var_sum {n : ℕ} (q : Fin n → I → ℝ) (hq : ∀ i, ∑ j, q i j = 1) (g : Fin n → I → ℝ)
    (hg0 : ∀ k, ∑ j, q k j * g k j = 0) :
    ∑ w : Fin n → I, (∏ m, q m (w m)) * (∑ k, g k (w k)) ^ 2 =
      ∑ k, ∑ j, q k j * g k j ^ 2 := by
  have key : ∀ k : Fin n, ∑ l : Fin n, ∑ w : Fin n → I, (∏ m, q m (w m)) *
      (g k (w k) * g l (w l)) = ∑ j, q k j * g k j ^ 2 := by
    intro k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have h1 : ∑ w : Fin n → I, (∏ m, q m (w m)) * (g k (w k) * g k (w k)) =
        ∑ j, q k j * g k j ^ 2 := by
      rw [exp_one q hq k (fun j => g k j * g k j)]
      simp only [sq]
    have h2 : ∑ l ∈ Finset.univ.erase k,
        ∑ w : Fin n → I, (∏ m, q m (w m)) * (g k (w k) * g l (w l)) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [exp_two q hq k l (Finset.ne_of_mem_erase hl).symm (g k) (g l), hg0, zero_mul]
    rw [h1, h2, add_zero]
  calc ∑ w : Fin n → I, (∏ m, q m (w m)) * (∑ k, g k (w k)) ^ 2
      = ∑ k : Fin n, ∑ l : Fin n, ∑ w : Fin n → I, (∏ m, q m (w m)) *
          (g k (w k) * g l (w l)) := by
        have e : ∀ w : Fin n → I, (∏ m, q m (w m)) * (∑ k, g k (w k)) ^ 2 =
            ∑ k : Fin n, ∑ l : Fin n, (∏ m, q m (w m)) * (g k (w k) * g l (w l)) := by
          intro w; rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
        simp only [e]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun k _ => key k

end X6ETM

namespace X6ETM

open X6TWL X6TER

attribute [local instance] Classical.propDecidable Classical.decEq

/-- per-letter variance in bits. -/
lemma var_bits (d : ℕ) (hd : 0 < d) (p : Fin d → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) :
    ∑ j, p j * (-Real.logb 2 (p j) - -∑ i, p i * Real.logb 2 (p i)) ^ 2 ≤ entropyConstant d := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv := X6ETV.var_bound d hd p hp0 hp
  have e : ∀ j, p j * (-Real.logb 2 (p j) - -∑ i, p i * Real.logb 2 (p i)) ^ 2 =
      p j * (Real.log (p j) + -∑ i, p i * Real.log (p i)) ^ 2 / Real.log 2 ^ 2 := by
    intro j
    simp only [Real.logb, ← Finset.sum_div, mul_div_assoc']
    field_simp
    ring
  simp only [e, ← Finset.sum_div]
  unfold entropyConstant
  rw [div_le_iff₀ (by positivity)]
  simp only [Real.logb, div_pow]
  rw [max_mul_of_nonneg _ _ (by positivity)]
  field_simp
  exact hv

end X6ETM

open X6TWL X6TER X6ETM

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (d : ℕ) (hd : 0 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ K ≤ entropyConstant d ∧ K = entropyConstant d ∧
    ∀ (n : ℕ), 0 < n → ∀ (S : Fin n → FineResolution d) (delta : ℝ), 0 < delta →
      effectProb (wordTensor (fun i => (S i).state)) (entropyProjector S delta) ≥ 1 - K / delta^2 := by
  have hK0 : 0 ≤ entropyConstant d := by unfold entropyConstant; positivity
  refine ⟨entropyConstant d, hK0, le_refl _, rfl, ?_⟩
  intro n hn S δ hδ
  set q : Fin n → Fin d → ℝ := fun i j => (S i).weight j
  have hq0 : ∀ i j, 0 ≤ q i j := fun i j => (S i).nonneg j
  have hq : ∀ i, ∑ j, q i j = 1 := fun i => (S i).total
  set W : (Fin n → Fin d) → ℝ := fun w => ∏ m, q m (w m)
  have hW0 : ∀ w, 0 ≤ W w := fun w => W_nonneg q hq0 w
  have hW1 : ∑ w, W w = 1 := total q hq
  set H : Fin n → ℝ := fun i => vnEntropy (S i).state
  have hH : ∀ i, H i = -∑ j, q i j * Real.logb 2 (q i j) := fun i => X6TCR.vn_state (S i)
  set g : Fin n → Fin d → ℝ := fun i j => -Real.logb 2 (q i j) - H i
  set E := Finset.univ.filter fun w : Fin n → Fin d =>
    (∀ i, 0 < ((S i).law (w i)).toReal) ∧
    |(∑ i, -Real.logb 2 ((S i).law (w i)).toReal) - ∑ i, vnEntropy (S i).state| ≤ δ * Real.sqrt n
  have hprob : effectProb (wordTensor (fun i => (S i).state)) (entropyProjector S δ) =
      ∑ w ∈ E, W w := by
    have hPi : entropyProjector S δ = ∑ w ∈ E, P S w := rfl
    rw [hPi]; unfold effectProb
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have := prob_P S w; unfold effectProb at this; rw [this]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hY : ∀ w : Fin n → Fin d, (∑ i, -Real.logb 2 ((S i).law (w i)).toReal) - ∑ i, vnEntropy (S i).state =
      ∑ i, g i (w i) := by
    intro w; simp only [g, law_eq, Finset.sum_sub_distrib, q, H]
  have hc : 0 < δ ^ 2 * n := by positivity
  -- Chebyshev
  have hbad : ∀ w ∉ E, W w ≤ W w * (∑ i, g i (w i)) ^ 2 / (δ ^ 2 * n) := by
    intro w hw
    rcases (hW0 w).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hall : ∀ i, 0 < ((S i).law (w i)).toReal := by
        intro i; rw [law_eq]
        rcases (hq0 i (w i)).eq_or_lt with h | h
        · exfalso
          have : W w = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h.symm
          linarith
        · exact h
      have hlt : δ * Real.sqrt n < |∑ i, g i (w i)| := by
        rw [← hY]
        by_contra hc'; push Not at hc'
        exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall, hc'⟩)
      have hsq : δ ^ 2 * n < (∑ i, g i (w i)) ^ 2 := by
        have h1 : 0 ≤ δ * Real.sqrt n := by positivity
        have := mul_self_lt_mul_self h1 hlt
        rw [abs_mul_abs_self, show δ * Real.sqrt n * (δ * Real.sqrt n) = δ ^ 2 * (Real.sqrt n) ^ 2 by ring,
          Real.sq_sqrt hn'.le] at this
        rw [sq (∑ i, g i (w i))]; exact this
      rw [le_div_iff₀ hc]
      exact mul_le_mul_of_nonneg_left hsq.le (hW0 w)
  have hg0 : ∀ k, ∑ j, q k j * g k j = 0 := by
    intro k
    simp only [g, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq, one_mul, hH]
    simp only [mul_neg, Finset.sum_neg_distrib, sub_self]
  have hvar : ∑ w, W w * (∑ i, g i (w i)) ^ 2 ≤ n * entropyConstant d := by
    rw [var_sum q hq g hg0]
    calc ∑ k, ∑ j, q k j * g k j ^ 2 ≤ ∑ _k : Fin n, entropyConstant d := by
          refine Finset.sum_le_sum fun k _ => ?_
          have := var_bits d hd (q k) (hq0 k) (hq k)
          simp only [g, hH]; exact this
      _ = n * entropyConstant d := by simp
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ E) W
  have hfE : Finset.univ.filter (fun w => w ∈ E) = E := by ext w; simp
  rw [hfE, hW1] at hsplit
  have hnot : ∑ w ∈ Finset.univ.filter (fun w => w ∉ E), W w ≤ entropyConstant d / δ ^ 2 := by
    calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w => w ∉ E), W w * (∑ i, g i (w i)) ^ 2 / (δ ^ 2 * n) :=
          Finset.sum_le_sum fun w hw => hbad w (Finset.mem_filter.mp hw).2
      _ ≤ ∑ w, W w * (∑ i, g i (w i)) ^ 2 / (δ ^ 2 * n) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => div_nonneg (mul_nonneg (hW0 w) (sq_nonneg _)) hc.le)
      _ = (∑ w, W w * (∑ i, g i (w i)) ^ 2) / (δ ^ 2 * n) := by rw [Finset.sum_div]
      _ ≤ (n * entropyConstant d) / (δ ^ 2 * n) := div_le_div_of_nonneg_right hvar hc.le
      _ = entropyConstant d / δ ^ 2 := by field_simp
  rw [hprob, ge_iff_le]
  linarith

