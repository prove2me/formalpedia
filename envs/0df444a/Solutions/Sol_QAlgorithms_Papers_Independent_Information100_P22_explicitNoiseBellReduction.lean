-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.explicitNoiseBellReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:22:37.968011+00:00
-- url     : https://prove2.me/submissions/7ae26ac8-a138-49ee-8441-3cb08ce6c45e

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section


def X7NB_sgn (z : F2) : ℂ := if z = 0 then 1 else -1

lemma X7NB_10 : (1 : F2) ≠ 0 := by decide
lemma X7NB_11 : (1 : F2) + 1 = 0 := by decide
lemma X7NB_01 (z : F2) : z = 0 ∨ z = 1 := by revert z; decide

lemma X7NB_sgn_add (x y : F2) : X7NB_sgn (x + y) = X7NB_sgn x * X7NB_sgn y := by
  rcases X7NB_01 x with rfl | rfl <;> rcases X7NB_01 y with rfl | rfl <;> simp [X7NB_sgn, X7NB_10, X7NB_11]

lemma X7NB_sgn_sum {ι : Type*} (s : Finset ι) (f : ι → F2) :
    X7NB_sgn (∑ i ∈ s, f i) = ∏ i ∈ s, X7NB_sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [X7NB_sgn]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, X7NB_sgn_add, ih]

lemma X7NB_sgn_inj {x y : F2} (h : X7NB_sgn x = X7NB_sgn y) : x = y := by
  rcases X7NB_01 x with rfl | rfl <;> rcases X7NB_01 y with rfl | rfl <;> simp [X7NB_sgn, X7NB_10] at h ⊢ <;> norm_num at h

lemma X7NB_sgn_ne (x : F2) : X7NB_sgn x ≠ 0 := by
  unfold X7NB_sgn; split_ifs <;> norm_num

lemma X7NB_bit_inj {x y : Bool} (h : bit x = bit y) : x = y := by
  cases x <;> cases y <;> simp [bit] at h ⊢

def X7NB_unbit (z : F2) : Bool := decide (z = 1)

lemma X7NB_bit_unbit (z : F2) : bit (X7NB_unbit z) = z := by
  rcases X7NB_01 z with rfl | rfl <;> simp [bit, X7NB_unbit, X7NB_10.symm]

lemma X7NB_had (x y : Bool) : QAlgorithms.hadamard x y = ((Real.sqrt 2)⁻¹ : ℂ) * X7NB_sgn (bit x * bit y) := by
  cases x <;> cases y <;> simp [QAlgorithms.hadamard, X7NB_sgn, bit]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

lemma X7NB_ite (q : F2) [Decidable (q = 0)] : (if q = 0 then (1:ℂ) else -1) = X7NB_sgn q := by
  unfold X7NB_sgn; split_ifs <;> rfl

lemma X7NB_tensorH {I : Type*} [Fintype I] (b c : I → Bool) :
    tensorOps (fun _ : I => QAlgorithms.hadamard) b c =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card I * X7NB_sgn (∑ i, bit (b i) * bit (c i)) := by
  unfold tensorOps
  simp_rw [X7NB_had]
  rw [Finset.prod_mul_distrib, X7NB_sgn_sum]
  simp

lemma X7NB_formula {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I)
    (hB : IsUnit G.B.det) (a c : I → Bool) :
    bellNormalizer G a c = ((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card I *
      X7NB_sgn (quadratic G.AS a + ∑ i, (∑ j, G.B j i * bit (a j)) * bit (c i) +
        quadratic G.AN c) := by
  have hBT : IsUnit G.B.transpose.det := by rwa [Matrix.det_transpose]
  set M := (G.B.transpose)⁻¹ with hM
  have iff1 : ∀ b : I → Bool, ((fun i => bit (a i)) = M.mulVec (fun i => bit (b i))) ↔
      (fun i => bit (b i)) = G.B.transpose.mulVec (fun i => bit (a i)) := by
    intro b; constructor
    · intro h; rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hBT, Matrix.one_mulVec]
    · intro h; rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hBT, Matrix.one_mulVec]
  set bs : I → Bool := fun i => X7NB_unbit (G.B.transpose.mulVec (fun i => bit (a i)) i) with hbs
  have hbs' : (fun i => bit (bs i)) = G.B.transpose.mulVec (fun i => bit (a i)) := by
    funext i; simp [hbs, X7NB_bit_unbit]
  have uniq : ∀ b : I → Bool, (fun i => bit (b i)) = G.B.transpose.mulVec (fun i => bit (a i)) ↔
      b = bs := by
    intro b; constructor
    · intro h; funext i; apply X7NB_bit_inj; rw [← hbs'] at h; exact congrFun h i
    · rintro rfl; exact hbs'
  unfold bellNormalizer czLayer
  rw [Matrix.mul_diagonal, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single bs]
  · have hL : linearLayer M a bs = 1 := by
      unfold linearLayer; rw [if_pos ((iff1 bs).2 hbs')]
    have hbi : ∀ i, bit (bs i) = ∑ j, G.B j i * bit (a j) := fun i => by
      rw [congrFun hbs' i]; simp [Matrix.mulVec, dotProduct]
    rw [hL, X7NB_tensorH, X7NB_ite, X7NB_ite]
    simp_rw [hbi]
    rw [X7NB_sgn_add, X7NB_sgn_add]
    ring
  · intro b _ hb
    have : linearLayer M a b = 0 := by
      unfold linearLayer; rw [if_neg]
      intro h; exact hb ((uniq b).1 ((iff1 b).1 h))
    rw [this, zero_mul]
  · simp



lemma X7NB_two (z : F2) : z + z = 0 := by rcases X7NB_01 z with rfl | rfl <;> decide

lemma X7NB_vtwo {I : Type*} (x : I → F2) : x + x = 0 := funext fun i => X7NB_two (x i)

lemma X7NB_sgn_zero : X7NB_sgn 0 = 1 := by simp [X7NB_sgn]

lemma X7NB_sgn_star (z : F2) : star (X7NB_sgn z) = X7NB_sgn z := by
  unfold X7NB_sgn; split_ifs <;> simp

lemma X7NB_sgn_I (s : F2) : X7NB_sgn s = Complex.I ^ (if s = 0 then 0 else 2) := by
  unfold X7NB_sgn; split_ifs <;> simp

def X7NB_bv {I : Type*} (a : I → Bool) : I → F2 := fun i => bit (a i)

def X7NB_bvE (I : Type*) : (I → Bool) ≃ (I → F2) where
  toFun := X7NB_bv
  invFun := fun x i => X7NB_unbit (x i)
  left_inv := fun a => funext fun i => X7NB_bit_inj (X7NB_bit_unbit _)
  right_inv := fun x => funext fun i => X7NB_bit_unbit (x i)

lemma X7NB_bvE_apply {I : Type*} (a : I → Bool) : X7NB_bvE I a = X7NB_bv a := rfl

lemma X7NB_bv_symm {I : Type*} (x : I → F2) : X7NB_bv ((X7NB_bvE I).symm x) = x :=
  (X7NB_bvE I).apply_symm_apply x

lemma X7NB_bv_inj {I : Type*} {a b : I → Bool} (h : X7NB_bv a = X7NB_bv b) : a = b :=
  (X7NB_bvE I).injective h

lemma X7NB_sum_bv {I : Type*} [Fintype I] [DecidableEq I] (f : (I → F2) → ℂ) :
    ∑ b : I → Bool, f (X7NB_bv b) = ∑ y : I → F2, f y := by
  exact Equiv.sum_comp (X7NB_bvE I) f

/-- ordering indicator -/
def X7NB_L {I : Type*} [Fintype I] (a b : I) : F2 :=
  if (Fintype.equivFin I a).val < (Fintype.equivFin I b).val then 1 else 0

def X7NB_Q {I : Type*} [Fintype I] (A : Matrix I I F2) (x : I → F2) : F2 :=
  ∑ a, ∑ b, X7NB_L a b * A a b * x a * x b

lemma X7NB_quad {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I F2) (z : I → Bool) :
    quadratic A z = X7NB_Q A (X7NB_bv z) := by
  unfold quadratic X7NB_Q X7NB_L X7NB_bv
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  split_ifs <;> simp_all

lemma X7NB_Lsum {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I F2)
    (hd : ∀ a, A a a = 0) (a b : I) : (X7NB_L a b + X7NB_L b a) * A a b = A a b := by
  by_cases h : a = b
  · subst h; simp [hd]
  · have hne : (Fintype.equivFin I a).val ≠ (Fintype.equivFin I b).val := by
      intro e; exact h ((Fintype.equivFin I).injective (Fin.ext e))
    unfold X7NB_L
    rcases lt_or_gt_of_ne hne with h1 | h1
    · rw [if_pos h1, if_neg (by omega)]; simp
    · rw [if_neg (by omega), if_pos h1]; simp

lemma X7NB_polar {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I F2)
    (hA : ∀ a b, A a b = A b a) (hd : ∀ a, A a a = 0) (y u : I → F2) :
    X7NB_Q A (y + u) = X7NB_Q A y + X7NB_Q A u + (A *ᵥ u) ⬝ᵥ y := by
  have e1 : X7NB_Q A (y + u) = X7NB_Q A y + X7NB_Q A u +
      ((∑ a, ∑ b, X7NB_L a b * A a b * y a * u b) + ∑ a, ∑ b, X7NB_L a b * A a b * u a * y b) := by
    unfold X7NB_Q
    simp only [← Finset.sum_add_distrib, Pi.add_apply]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  have e2 : (∑ a, ∑ b, X7NB_L a b * A a b * u a * y b) =
      ∑ a, ∑ b, X7NB_L b a * A a b * y a * u b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hA b a]; ring
  have e3 : (A *ᵥ u) ⬝ᵥ y = ∑ a, ∑ b, A a b * y a * u b := by
    simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have := X7NB_Lsum A hd a b
  linear_combination y a * u b * this

lemma X7NB_Q_zero {I : Type*} [Fintype I] (A : Matrix I I F2) : X7NB_Q A 0 = 0 := by
  simp [X7NB_Q]

lemma X7NB_sumF2 (f : F2 → ℂ) : ∑ z : F2, f z = f 0 + f 1 := by
  exact Fin.sum_univ_two f

lemma X7NB_char {I : Type*} [Fintype I] [DecidableEq I] (r : I → F2) :
    ∑ y : I → F2, X7NB_sgn (r ⬝ᵥ y) = if r = 0 then (2:ℂ) ^ Fintype.card I else 0 := by
  have h1 : ∀ y : I → F2, X7NB_sgn (r ⬝ᵥ y) = ∏ i, X7NB_sgn (r i * y i) := by
    intro y; rw [dotProduct, X7NB_sgn_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i z => X7NB_sgn (r i * z))]
  have h2 : ∀ i, ∑ z : F2, X7NB_sgn (r i * z) = if r i = 0 then 2 else 0 := by
    intro i
    rw [X7NB_sumF2]
    rcases X7NB_01 (r i) with h | h <;> rw [h] <;> simp [X7NB_sgn, X7NB_10] <;> norm_num
  simp_rw [h2]
  by_cases hr : r = 0
  · rw [if_pos hr]; simp [hr]
  · rw [if_neg hr]
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hr (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma X7NB_sqrtpow (n : ℕ) : Real.sqrt ((2:ℝ)^n) = (Real.sqrt 2)^n := by
  rw [show (2:ℝ)^n = ((Real.sqrt 2)^n)^2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (by positivity)

def X7NB_κ (I : Type*) [Fintype I] : ℂ := ((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card I

lemma X7NB_κ_star (I : Type*) [Fintype I] : star (X7NB_κ I) = X7NB_κ I := by
  unfold X7NB_κ; simp [star_pow, Complex.conj_ofReal]

lemma X7NB_κ_sq (I : Type*) [Fintype I] : X7NB_κ I * X7NB_κ I * (2:ℂ) ^ Fintype.card I = 1 := by
  unfold X7NB_κ
  rw [← mul_pow, ← mul_pow]
  have : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * 2 = 1 := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
    rw [← h2]; field_simp
  rw [this, one_pow]

lemma X7NB_dotT {I : Type*} [Fintype I] (B : Matrix I I F2) (x u : I → F2) :
    (B.transpose *ᵥ x) ⬝ᵥ u = (B *ᵥ u) ⬝ᵥ x := by
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, dotProduct_comm]

lemma X7NB_U {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I)
    (hB : IsUnit G.B.det) (a c : I → Bool) :
    bellNormalizer G a c = X7NB_κ I * X7NB_sgn (X7NB_Q G.AS (X7NB_bv a) +
      (G.B.transpose *ᵥ X7NB_bv a) ⬝ᵥ X7NB_bv c + X7NB_Q G.AN (X7NB_bv c)) := by
  rw [X7NB_formula G hB, X7NB_quad, X7NB_quad]
  rfl

def X7NB_P {I : Type*} [Fintype I] (u v : I → F2) : Matrix (I → Bool) (I → Bool) ℂ :=
  fun b b' => if X7NB_bv b = X7NB_bv b' + u then X7NB_sgn (v ⬝ᵥ X7NB_bv b') else 0

lemma X7NB_P00 {I : Type*} [Fintype I] [DecidableEq I] : X7NB_P (0 : I → F2) 0 = 1 := by
  ext a b
  unfold X7NB_P
  rw [Matrix.one_apply]
  by_cases h : a = b
  · subst h; rw [if_pos (by simp), if_pos rfl]; simp [X7NB_sgn_zero]
  · rw [if_neg (fun e => h (X7NB_bv_inj (by simpa using e))), if_neg h]

lemma X7NB_conj_entry {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I)
    (hB : IsUnit G.B.det) (u v : I → F2) (a a' : I → Bool) :
    (bellNormalizer G * X7NB_P u v * (bellNormalizer G)ᴴ) a a' =
      if G.B.transpose *ᵥ (X7NB_bv a + X7NB_bv a') + G.AN *ᵥ u + v = 0 then
        X7NB_sgn (X7NB_Q G.AS (X7NB_bv a) + X7NB_Q G.AS (X7NB_bv a') +
          (G.B.transpose *ᵥ X7NB_bv a) ⬝ᵥ u + X7NB_Q G.AN u) else 0 := by
  rw [Matrix.mul_apply]
  have hin : ∀ b' : I → Bool, (bellNormalizer G * X7NB_P u v) a b' =
      bellNormalizer G a ((X7NB_bvE I).symm (X7NB_bv b' + u)) * X7NB_sgn (v ⬝ᵥ X7NB_bv b') := by
    intro b'
    rw [Matrix.mul_apply, Finset.sum_eq_single ((X7NB_bvE I).symm (X7NB_bv b' + u))]
    · unfold X7NB_P; rw [if_pos (X7NB_bv_symm _)]
    · intro b _ hb
      unfold X7NB_P
      rw [if_neg, mul_zero]
      intro e; apply hb; rw [← e]; exact ((X7NB_bvE I).symm_apply_apply b).symm
    · simp
  simp_rw [hin, Matrix.conjTranspose_apply, X7NB_U G hB, X7NB_bv_symm, star_mul', X7NB_κ_star,
    X7NB_sgn_star]
  rw [X7NB_sum_bv (fun y => X7NB_κ I * X7NB_sgn (X7NB_Q G.AS (X7NB_bv a) +
      (G.B.transpose *ᵥ X7NB_bv a) ⬝ᵥ (y + u) + X7NB_Q G.AN (y + u)) * X7NB_sgn (v ⬝ᵥ y) *
      (X7NB_κ I * X7NB_sgn (X7NB_Q G.AS (X7NB_bv a') + (G.B.transpose *ᵥ X7NB_bv a') ⬝ᵥ y +
        X7NB_Q G.AN y)))]
  set C := X7NB_Q G.AS (X7NB_bv a) + X7NB_Q G.AS (X7NB_bv a') +
          (G.B.transpose *ᵥ X7NB_bv a) ⬝ᵥ u + X7NB_Q G.AN u with hC
  set r := G.B.transpose *ᵥ (X7NB_bv a + X7NB_bv a') + G.AN *ᵥ u + v with hr
  have hterm : ∀ y : I → F2, X7NB_κ I * X7NB_sgn (X7NB_Q G.AS (X7NB_bv a) +
      (G.B.transpose *ᵥ X7NB_bv a) ⬝ᵥ (y + u) + X7NB_Q G.AN (y + u)) * X7NB_sgn (v ⬝ᵥ y) *
      (X7NB_κ I * X7NB_sgn (X7NB_Q G.AS (X7NB_bv a') + (G.B.transpose *ᵥ X7NB_bv a') ⬝ᵥ y +
        X7NB_Q G.AN y)) = (X7NB_κ I * X7NB_κ I * X7NB_sgn C) * X7NB_sgn (r ⬝ᵥ y) := by
    intro y
    have hE : X7NB_Q G.AS (X7NB_bv a) + (G.B.transpose *ᵥ X7NB_bv a) ⬝ᵥ (y + u) +
        X7NB_Q G.AN (y + u) + v ⬝ᵥ y + (X7NB_Q G.AS (X7NB_bv a') +
        (G.B.transpose *ᵥ X7NB_bv a') ⬝ᵥ y + X7NB_Q G.AN y) = C + r ⬝ᵥ y := by
      rw [X7NB_polar G.AN G.symN G.diagN, hC, hr]
      simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
      linear_combination X7NB_two (X7NB_Q G.AN y)
    have h2 := congrArg X7NB_sgn hE
    simp only [X7NB_sgn_add] at h2 ⊢
    linear_combination (X7NB_κ I * X7NB_κ I) * h2
  simp_rw [hterm]
  rw [← Finset.mul_sum, X7NB_char]
  split_ifs
  · rw [mul_comm (X7NB_κ I * X7NB_κ I), mul_assoc, X7NB_κ_sq, mul_one]
  · rw [mul_zero]

lemma X7NB_charsub {I : Type*} (x t : I → F2) : x + t = 0 ↔ x = t := by
  constructor
  · intro h
    calc x = x + (t + t) := by rw [X7NB_vtwo, add_zero]
      _ = (x + t) + t := by rw [add_assoc]
      _ = t := by rw [h, zero_add]
  · rintro rfl; exact X7NB_vtwo x

lemma X7NB_conj {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I)
    (hB : IsUnit G.B.det) (u v : I → F2) :
    bellNormalizer G * X7NB_P u v * (bellNormalizer G)ᴴ =
      X7NB_sgn (X7NB_Q G.AS ((G.B.transpose)⁻¹ *ᵥ (G.AN *ᵥ u + v)) +
        (G.B.transpose *ᵥ ((G.B.transpose)⁻¹ *ᵥ (G.AN *ᵥ u + v))) ⬝ᵥ u + X7NB_Q G.AN u) •
      X7NB_P ((G.B.transpose)⁻¹ *ᵥ (G.AN *ᵥ u + v))
        (G.AS *ᵥ ((G.B.transpose)⁻¹ *ᵥ (G.AN *ᵥ u + v)) + G.B *ᵥ u) := by
  have hBT : IsUnit G.B.transpose.det := by rwa [Matrix.det_transpose]
  set w := (G.B.transpose)⁻¹ *ᵥ (G.AN *ᵥ u + v) with hw
  ext a a'
  rw [X7NB_conj_entry G hB, Matrix.smul_apply, smul_eq_mul]
  unfold X7NB_P
  have hiff : G.B.transpose *ᵥ (X7NB_bv a + X7NB_bv a') + G.AN *ᵥ u + v = 0 ↔
      X7NB_bv a = X7NB_bv a' + w := by
    rw [add_assoc, X7NB_charsub]
    constructor
    · intro h
      have : X7NB_bv a + X7NB_bv a' = w := by
        rw [hw, ← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hBT, Matrix.one_mulVec]
      rw [← this, add_comm (X7NB_bv a), ← add_assoc, X7NB_vtwo, zero_add]
    · intro h
      rw [h, add_comm (X7NB_bv a'), add_assoc, X7NB_vtwo, add_zero, hw, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hBT, Matrix.one_mulVec]
  by_cases h : X7NB_bv a = X7NB_bv a' + w
  · rw [if_pos (hiff.2 h), if_pos h, ← X7NB_sgn_add]
    congr 1
    rw [h, X7NB_polar G.AS G.symS G.diagS]
    simp only [Matrix.mulVec_add, add_dotProduct]
    rw [X7NB_dotT G.B (X7NB_bv a') u]
    linear_combination X7NB_two (X7NB_Q G.AS (X7NB_bv a'))
  · rw [if_neg (fun e => h (hiff.1 e)), if_neg h, mul_zero]

def X7NB_σ : Option Axis → Op Bool
  | none => 1
  | some a => axisMatrix a

def X7NB_uax : Option Axis → F2
  | none => 0
  | some .X => 1
  | some .Y => 1
  | some .Z => 0

def X7NB_vax : Option Axis → F2
  | none => 0
  | some .X => 0
  | some .Y => 1
  | some .Z => 1

def X7NB_eax : Option Axis → ℕ
  | some .Y => 1
  | _ => 0

lemma X7NB_site (t : Option Axis) (a b : Bool) :
    X7NB_σ t a b = Complex.I ^ X7NB_eax t *
      (if bit a = bit b + X7NB_uax t then X7NB_sgn (X7NB_vax t * bit b) else 0) := by
  rcases t with _ | ⟨_ | _ | _⟩ <;> cases a <;> cases b <;>
    simp [X7NB_σ, X7NB_eax, X7NB_uax, X7NB_vax, axisMatrix, bit, X7NB_sgn, pauliX, pauliY, pauliZ,
      Matrix.one_apply, X7NB_10, X7NB_11, X7NB_10.symm] <;> decide

lemma X7NB_tensor {I : Type*} [Fintype I] [DecidableEq I] (l : I → Option Axis) :
    tensorOps (fun i => X7NB_σ (l i)) =
      Complex.I ^ (∑ i, X7NB_eax (l i)) • X7NB_P (fun i => X7NB_uax (l i)) (fun i => X7NB_vax (l i)) := by
  ext a b
  unfold tensorOps
  rw [Matrix.smul_apply, smul_eq_mul]
  simp_rw [X7NB_site]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 1
  unfold X7NB_P
  by_cases h : ∀ i, bit (a i) = bit (b i) + X7NB_uax (l i)
  · rw [if_pos (show X7NB_bv a = X7NB_bv b + _ from funext h)]
    rw [Finset.prod_congr rfl (fun i _ => if_pos (h i))]
    rw [dotProduct, X7NB_sgn_sum]
    rfl
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    rw [if_neg (fun e => hi (congrFun e i))]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

def X7NB_tOf (x y : F2) : Option Axis :=
  if x = 0 then (if y = 0 then none else some .Z) else (if y = 0 then some .X else some .Y)

lemma X7NB_tOf_u (x y : F2) : X7NB_uax (X7NB_tOf x y) = x := by
  rcases X7NB_01 x with rfl | rfl <;> rcases X7NB_01 y with rfl | rfl <;>
    simp [X7NB_tOf, X7NB_uax, X7NB_10]

lemma X7NB_tOf_v (x y : F2) : X7NB_vax (X7NB_tOf x y) = y := by
  rcases X7NB_01 x with rfl | rfl <;> rcases X7NB_01 y with rfl | rfl <;>
    simp [X7NB_tOf, X7NB_vax, X7NB_10]

lemma X7NB_I_mod (N : ℕ) : Complex.I ^ (N % 4) = Complex.I ^ N := by
  conv_rhs => rw [← Nat.div_add_mod N 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

lemma X7NB_clifford {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I)
    (hB : IsUnit G.B.det) : RegisterClifford (bellNormalizer G) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    have := X7NB_conj G hB 0 0
    rw [X7NB_P00, Matrix.mul_one] at this
    rw [this]
    simp [X7NB_Q_zero, X7NB_sgn_zero, X7NB_P00]
  · intro l
    obtain ⟨w, v', s, hc⟩ : ∃ w v' : I → F2, ∃ s : F2,
        bellNormalizer G * X7NB_P (fun i => X7NB_uax (l i)) (fun i => X7NB_vax (l i)) *
          (bellNormalizer G)ᴴ = X7NB_sgn s • X7NB_P w v' := ⟨_, _, _, X7NB_conj G hB _ _⟩
    let t : I → Option Axis := fun i => X7NB_tOf (w i) (v' i)
    have ht := X7NB_tensor t
    have hu : (fun i => X7NB_uax (t i)) = w := funext fun i => X7NB_tOf_u _ _
    have hv : (fun i => X7NB_vax (t i)) = v' := funext fun i => X7NB_tOf_v _ _
    rw [hu, hv] at ht
    have hP : X7NB_P w v' = Complex.I ^ (3 * ∑ i, X7NB_eax (t i)) •
        tensorOps (fun i => X7NB_σ (t i)) := by
      rw [ht, smul_smul, ← pow_add,
        show 3 * (∑ i, X7NB_eax (t i)) + (∑ i, X7NB_eax (t i)) = 4 * ∑ i, X7NB_eax (t i) by ring,
        pow_mul, Complex.I_pow_four, one_pow, one_smul]
    let N := (∑ i, X7NB_eax (l i)) + (if s = 0 then 0 else 2) + 3 * (∑ i, X7NB_eax (t i))
    have key : bellNormalizer G * tensorOps (fun i => X7NB_σ (l i)) * (bellNormalizer G)ᴴ =
        Complex.I ^ (N % 4) • tensorOps (fun i => X7NB_σ (t i)) := by
      rw [X7NB_tensor l, Matrix.mul_smul, Matrix.smul_mul, hc, hP, X7NB_sgn_I, smul_smul,
        smul_smul, ← pow_add, ← pow_add, X7NB_I_mod]
    refine ⟨t, ⟨N % 4, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    exact key

lemma X7NB_bell {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I)
    (hB : IsUnit G.B.det) :
    act (Matrix.kronecker (1 : Op (I → Bool)) (bellNormalizer G)) (graphVector G) =
      bell (I → Bool) := by
  have hBT : IsUnit G.B.transpose.det := by rwa [Matrix.det_transpose]
  ext ⟨x, y⟩
  simp only [act, bell, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    WithLp.ofLp_toLp]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp only [Matrix.one_apply_eq, one_mul]
    have hg : ∀ c : I → Bool, (graphVector G) (x, c) = ((2 : ℂ) ^ Fintype.card I)⁻¹ *
        X7NB_sgn (X7NB_Q G.AS (X7NB_bv x) + (G.B.transpose *ᵥ X7NB_bv x) ⬝ᵥ X7NB_bv c +
          X7NB_Q G.AN (X7NB_bv c)) := by
      intro c
      simp only [graphVector, WithLp.ofLp_toLp]
      rw [X7NB_ite, X7NB_quad, X7NB_quad]
      congr 3
      congr 1
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, X7NB_bv, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
      ring
    simp_rw [hg, X7NB_U G hB]
    rw [X7NB_sum_bv (fun z => X7NB_κ I * X7NB_sgn (X7NB_Q G.AS (X7NB_bv y) +
        (G.B.transpose *ᵥ X7NB_bv y) ⬝ᵥ z + X7NB_Q G.AN z) * (((2 : ℂ) ^ Fintype.card I)⁻¹ *
        X7NB_sgn (X7NB_Q G.AS (X7NB_bv x) + (G.B.transpose *ᵥ X7NB_bv x) ⬝ᵥ z + X7NB_Q G.AN z)))]
    have hterm : ∀ z : I → F2, X7NB_κ I * X7NB_sgn (X7NB_Q G.AS (X7NB_bv y) +
        (G.B.transpose *ᵥ X7NB_bv y) ⬝ᵥ z + X7NB_Q G.AN z) * (((2 : ℂ) ^ Fintype.card I)⁻¹ *
        X7NB_sgn (X7NB_Q G.AS (X7NB_bv x) + (G.B.transpose *ᵥ X7NB_bv x) ⬝ᵥ z + X7NB_Q G.AN z)) =
        (X7NB_κ I * ((2 : ℂ) ^ Fintype.card I)⁻¹ *
          X7NB_sgn (X7NB_Q G.AS (X7NB_bv y) + X7NB_Q G.AS (X7NB_bv x))) *
          X7NB_sgn ((G.B.transpose *ᵥ (X7NB_bv y + X7NB_bv x)) ⬝ᵥ z) := by
      intro z
      have hE : X7NB_Q G.AS (X7NB_bv y) + (G.B.transpose *ᵥ X7NB_bv y) ⬝ᵥ z + X7NB_Q G.AN z +
          (X7NB_Q G.AS (X7NB_bv x) + (G.B.transpose *ᵥ X7NB_bv x) ⬝ᵥ z + X7NB_Q G.AN z) =
          X7NB_Q G.AS (X7NB_bv y) + X7NB_Q G.AS (X7NB_bv x) +
            (G.B.transpose *ᵥ (X7NB_bv y + X7NB_bv x)) ⬝ᵥ z := by
        simp only [Matrix.mulVec_add, add_dotProduct]
        linear_combination X7NB_two (X7NB_Q G.AN z)
      have h2 := congrArg X7NB_sgn hE
      simp only [X7NB_sgn_add] at h2 ⊢
      linear_combination (X7NB_κ I * ((2 : ℂ) ^ Fintype.card I)⁻¹) * h2
    simp_rw [hterm]
    rw [← Finset.mul_sum, X7NB_char]
    have hiff : G.B.transpose *ᵥ (X7NB_bv y + X7NB_bv x) = 0 ↔ x = y := by
      constructor
      · intro h
        have : X7NB_bv y + X7NB_bv x = 0 := by
          have := congrArg (fun z => (G.B.transpose)⁻¹ *ᵥ z) h
          simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hBT] using this
        exact (X7NB_bv_inj ((X7NB_charsub _ _).1 this)).symm
      · rintro rfl; rw [X7NB_vtwo, Matrix.mulVec_zero]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos (hiff.2 rfl), if_pos rfl, X7NB_two, X7NB_sgn_zero, mul_one, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), mul_one]
      unfold X7NB_κ
      rw [Fintype.card_fun, Fintype.card_bool]
      push_cast
      rw [X7NB_sqrtpow]
      push_cast
      rw [inv_pow]
    · rw [if_neg (fun h => hxy (hiff.1 h)), if_neg hxy, mul_zero]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
  · simp

end

end QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : QAlgorithms.Papers.Independent.Information100.P22.CutGraph I) :
    Fintype (QAlgorithms.Papers.Independent.Information100.P22.cutKernel G) := Fintype.ofFinite _

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 in
theorem solution (nu : ℕ) (hnu : 1 ≤ nu) (G : CutGraph (Fin nu))
    (hB : IsUnit G.B.det) :
    RegisterClifford (bellNormalizer G) ∧
    act (Matrix.kronecker (1 : Op (Qubits nu)) (bellNormalizer G)) (graphVector G) =
      bell (Qubits nu) :=
  ⟨X7NB_clifford G hB, X7NB_bell G hB⟩

end
