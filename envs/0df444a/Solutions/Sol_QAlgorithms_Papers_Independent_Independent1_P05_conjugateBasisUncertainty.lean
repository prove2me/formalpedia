-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P05.conjugateBasisUncertainty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:57.362362+00:00
-- url     : https://prove2.me/submissions/372fc356-e2dc-4194-9f57-65f92c20bc5b

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model

noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate MatrixOrder
open QAlgorithms

namespace NLTSUncertainty

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def cut (S : Finset ι) (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => if i ∈ S then v i else 0

private lemma cut_sq (S : Finset ι) (v : EuclideanSpace ℂ ι) :
    ‖cut S v‖ ^ 2 = ∑ i ∈ S, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i : ι, ‖if i ∈ S then v i else 0‖ ^ 2) = _
  calc
    _ = ∑ i : ι, if i ∈ S then ‖v i‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _; split_ifs <;> simp
    _ = _ := by simp

private lemma cut_le (S : Finset ι) (v : EuclideanSpace ℂ ι) : ‖cut S v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [cut_sq, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)

omit [Fintype ι] in
private lemma cut_sub (S : Finset ι) (v w : EuclideanSpace ℂ ι) :
    cut S (v-w) = cut S v - cut S w := by
  ext i; simp [cut]; split_ifs <;> simp

private lemma cut_compl (S : Finset ι) (v : EuclideanSpace ℂ ι) :
    ‖v - cut S v‖ ^ 2 = ‖v‖ ^ 2 - ‖cut S v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, cut_sq]
  have he : (∑ i : ι, ‖(v - cut S v) i‖ ^ 2) + ∑ i ∈ S, ‖v i‖ ^ 2 =
      ∑ i : ι, ‖v i‖ ^ 2 := by
    have hs : (∑ i : ι, if i ∈ S then ‖v i‖ ^ 2 else 0) = ∑ i ∈ S, ‖v i‖ ^ 2 := by simp
    rw [← hs, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; by_cases h : i ∈ S <;> simp [cut,h]
  linarith

omit [DecidableEq ι] in
private lemma act_sub (U : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    act U (v-w) = act U v - act U w := by
  ext i; simp [act, Matrix.mulVec_sub]

private lemma supported_bound [Nonempty ι] (U : Matrix ι ι ℂ) (c : ℝ)
    (hc : ∀ i j, ‖U i j‖ ^ 2 = c) (S T : Finset ι) (v : EuclideanSpace ℂ ι) :
    ‖cut T (act U (cut S v))‖ ^ 2 ≤
      (S.card : ℝ) * T.card * c * ‖v‖ ^ 2 := by
  have hcn : 0 ≤ c := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    rw [← hc i i]; positivity
  have hi (i : ι) : ‖act U (cut S v) i‖ ^ 2 ≤
      (S.card : ℝ) * c * ‖v‖ ^ 2 := by
    have he : act U (cut S v) i = ∑ j ∈ S, U i j * v j := by
      simp [act, Matrix.mulVec, dotProduct, cut, Finset.sum_ite_mem]
    have hnorm : ‖∑ j ∈ S, U i j * v j‖ ≤ ∑ j ∈ S, ‖U i j‖ * ‖v j‖ := by
      simpa only [norm_mul] using norm_sum_le S (fun j => U i j * v j)
    calc
      ‖act U (cut S v) i‖ ^ 2 = ‖∑ j ∈ S, U i j * v j‖ ^ 2 := by rw [he]
      _ ≤ (∑ j ∈ S, ‖U i j‖ * ‖v j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ (∑ j ∈ S, ‖U i j‖ ^ 2) * (∑ j ∈ S, ‖v j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq S _ _
      _ = (S.card : ℝ) * c * ‖cut S v‖ ^ 2 := by simp_rw [hc]; rw [cut_sq]; simp
      _ ≤ (S.card : ℝ) * c * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (cut_le S v) 2)
          (by positivity)
  rw [cut_sq]
  calc
    (∑ i ∈ T, ‖act U (cut S v) i‖ ^ 2) ≤
        ∑ _i ∈ T, (S.card : ℝ) * c * ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp; ring

private lemma pure_bound [Nonempty ι] (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (c : ℝ) (hc : ∀ i j, ‖U i j‖ ^ 2 = c) (S T : Finset ι)
    (v : EuclideanSpace ℂ ι) :
    ‖cut T (act U v)‖ ^ 2 ≤
      (S.card : ℝ) * T.card * c * ‖v‖ ^ 2 + 2 * ‖v‖ * ‖v-cut S v‖ := by
  let x := cut T (act U v)
  let y := cut T (act U (cut S v))
  have hx : ‖x‖ ≤ ‖v‖ := (cut_le _ _).trans (le_of_eq (act_norm_of_mem_unitaryGroup hU v))
  have hy : ‖y‖ ≤ ‖v‖ := (cut_le _ _).trans
    ((le_of_eq (act_norm_of_mem_unitaryGroup hU _)).trans (cut_le S v))
  have hd : ‖x‖ - ‖y‖ ≤ ‖v-cut S v‖ := by
    refine (norm_sub_norm_le x y).trans ?_
    rw [show x-y = cut T (act U (v-cut S v)) by rw [act_sub,cut_sub]]
    exact (cut_le _ _).trans (le_of_eq (act_norm_of_mem_unitaryGroup hU _))
  have hdiff : ‖x‖ ^ 2 - ‖y‖ ^ 2 ≤ 2*‖v‖*‖v-cut S v‖ := by
    calc
      ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖-‖y‖)*(‖x‖+‖y‖) := by ring
      _ ≤ ‖v-cut S v‖*(‖x‖+‖y‖) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ ‖v-cut S v‖*(2*‖v‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ = _ := by ring
  have hb := supported_bound U c hc S T v
  change ‖x‖ ^ 2 ≤ _
  change ‖y‖ ^ 2 ≤ _ at hb
  linarith

private def col (A : Matrix ι ι ℂ) (j : ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => A i j

private def mass (rho : Matrix ι ι ℂ) (S : Finset ι) : ℝ := ∑ i ∈ S, (rho i i).re

private lemma gram_mass (A : Matrix ι ι ℂ) (S : Finset ι) :
    mass (A * star A) S = ∑ j : ι, ‖cut S (col A j)‖ ^ 2 := by
  simp only [mass, Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, cut_sq]
  change (∑ i ∈ S, ∑ j : ι, Complex.normSq (A i j)) =
    ∑ j : ι, ∑ i ∈ S, ‖A i j‖ ^ 2
  simp_rw [Complex.normSq_eq_norm_sq]
  exact Finset.sum_comm

private lemma gram_total (A : Matrix ι ι ℂ) :
    (A * star A).trace.re = ∑ j : ι, ‖col A j‖ ^ 2 := by
  simpa [mass, Matrix.trace, cut] using gram_mass A Finset.univ

omit [DecidableEq ι] in
private lemma col_mul (U A : Matrix ι ι ℂ) (j : ι) : col (U*A) j = act U (col A j) := by
  ext i; rfl

private lemma mixed_bound [Nonempty ι] (rho : Matrix ι ι ℂ) (hrho : IsDensityMatrix rho)
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (c : ℝ) (hc : ∀ i j, ‖U i j‖ ^ 2 = c) (S T : Finset ι) :
    mass (U*rho*star U) T ≤ 2*Real.sqrt (1-mass rho S) +
      (S.card : ℝ)*T.card*c := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hrho.1.nonneg
  let A := star B
  have hA : rho = A * star A := by simpa [A] using hB
  have ht : (∑ j : ι, ‖col A j‖ ^ 2) = 1 := by
    rw [← gram_total, ← hA,hrho.2]; rfl
  have hp : (∑ j : ι, ‖col A j-cut S (col A j)‖ ^ 2) = 1-mass rho S := by
    simp_rw [cut_compl]
    rw [Finset.sum_sub_distrib,ht,← gram_mass,← hA]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun j => ‖col A j‖) (fun j => ‖col A j-cut S (col A j)‖)
  rw [ht,hp,Real.sqrt_one,one_mul] at hcs
  have hm : U*rho*star U = (U*A)*star (U*A) := by rw [hA,star_mul]; simp [mul_assoc]
  rw [hm,gram_mass]
  simp_rw [col_mul]
  calc
    (∑ j : ι, ‖cut T (act U (col A j))‖ ^ 2) ≤
        ∑ j : ι, ((S.card : ℝ)*T.card*c*‖col A j‖ ^ 2 +
          2*‖col A j‖*‖col A j-cut S (col A j)‖) :=
      Finset.sum_le_sum fun j _ => pure_bound U hU c hc S T (col A j)
    _ = (S.card : ℝ)*T.card*c +
        2*(∑ j : ι, ‖col A j‖*‖col A j-cut S (col A j)‖) := by
      simp_rw [mul_assoc (2 : ℝ)]
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,ht]; ring
    _ ≤ _ := by linarith

private def sgn (b : Bool) : ℂ := if b then -1 else 1

private lemma sgn_add (a b : Bool) : sgn (a + b) = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num [sgn, Bool.add_eq_xor, Bool.zero_eq_false]

private lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn, Bool.zero_eq_false]
  | @insert a s ha ih => simp [ha, sgn_add, ih]

private lemma char_orth (n : ℕ) (a b : Qubits n) :
    (∑ i : Qubits n, sgn (dotBits a i) * sgn (dotBits b i)) =
      if a = b then (2 : ℂ)^n else 0 := by
  classical
  simp_rw [dotBits, sgn_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k v => sgn (a k && v) * sgn (b k && v))]
  have h (k : Fin n) :
      (∑ v : Bool, sgn (a k && v) * sgn (b k && v)) =
        if a k = b k then (2 : ℂ) else 0 := by
    cases a k <;> cases b k <;> norm_num [sgn, Bool.add_eq_xor, Bool.zero_eq_false]
  simp_rw [h]
  by_cases hab : a = b
  · subst b; simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

private lemma normalization (n : ℕ) :
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)) ^ 2 * (2 : ℂ)^n = 1 := by
  have h : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 * 2 = 1 := by
    have hsq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have : ((Real.sqrt (2 : ℝ))⁻¹)^2 * 2 = 1 := by field_simp; nlinarith
    exact_mod_cast this
  push_cast at h ⊢
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, h, one_pow]

private lemma hadamard_involutive (n : ℕ) : hadamardN n * hadamardN n = 1 := by
  classical
  have he (a b : Qubits n) : hadamardN n a b =
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * sgn (dotBits a b) := by
    have hc : dotBits b a = dotBits a b := by simp [dotBits, Bool.and_comm]
    simp only [hadamardN, Matrix.of_apply, hc, sgn]
    split_ifs <;> ring
  ext a b
  simp_rw [Matrix.mul_apply, he]
  have hc (i : Qubits n) : dotBits i b = dotBits b i := by simp [dotBits, Bool.and_comm]
  simp_rw [hc]
  simp_rw [show ∀ u v : ℂ, (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * u *
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * v) =
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ))^2 * (u * v) by intros; ring]
  rw [← Finset.mul_sum, char_orth]
  by_cases h : a = b
  · subst b
    simpa only [ite_true, Matrix.one_apply_eq] using normalization n
  · simp [h]


private lemma had_unitary (n : ℕ) : hadamardN n ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [hadamardN_star, hadamard_involutive]


private lemma had_flat (n : ℕ) (i j : Qubits n) :
    ‖hadamardN n i j‖ ^ 2 = 1/(2 : ℝ)^n := by
  have hs : (((Real.sqrt 2)⁻¹ ^ n : ℝ)) ^ 2 = 1/(2 : ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, inv_pow, Real.sq_sqrt (by norm_num)]
    simp [one_div, inv_pow]
  simp only [hadamardN, Matrix.of_apply]
  split_ifs <;> simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using hs

private lemma bits_inj (n : ℕ) : Function.Injective (@bitsOfZMod n) := by
  intro a b h
  funext i
  have hi := congrFun h i
  have cases2 (z : ZMod 2) : z = 0 ∨ z = 1 := by
    fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases cases2 (a i) with ha | ha <;> rcases cases2 (b i) with hb | hb <;>
    simp_all [bitsOfZMod]

private lemma mass_image {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (had : Bool) (S : Finset (Fin n → ZMod 2)) :
    mass (if had then hadamardN n*rho*star (hadamardN n) else rho)
      (S.image bitsOfZMod) =
      QAlgorithms.Papers.Independent.Independent1.P05.nltsMass rho had S := by
  rw [mass,Finset.sum_image (bits_inj n).injOn]
  rfl

end NLTSUncertainty

open QAlgorithms.Papers.Independent.Independent1.P05

theorem solution {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (hrho : IsDensityMatrix rho) (S T : Finset (NLTSWord n)) :
    nltsMass rho true T ≤ 2*Real.sqrt (1-nltsMass rho false S) +
      (S.card : ℝ)*T.card/(2 : ℝ)^n := by
  have h := NLTSUncertainty.mixed_bound rho hrho (hadamardN n)
    (NLTSUncertainty.had_unitary n) (1/(2 : ℝ)^n) (NLTSUncertainty.had_flat n)
    (S.image bitsOfZMod) (T.image bitsOfZMod)
  have hT : NLTSUncertainty.mass (hadamardN n*rho*star (hadamardN n))
      (T.image bitsOfZMod) = nltsMass rho true T := NLTSUncertainty.mass_image rho true T
  have hS : NLTSUncertainty.mass rho (S.image bitsOfZMod) = nltsMass rho false S :=
    NLTSUncertainty.mass_image rho false S
  rw [hT,hS] at h
  simpa only [Finset.card_image_of_injective _ (NLTSUncertainty.bits_inj n),mul_one_div] using h
