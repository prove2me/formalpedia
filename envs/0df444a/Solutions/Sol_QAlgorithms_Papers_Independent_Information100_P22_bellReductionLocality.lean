-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.bellReductionLocality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:30:23.922522+00:00
-- url     : https://prove2.me/submissions/642363f7-e3e7-49b8-97a8-58187ffcfd69

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section


def X7BL_sgn (z : F2) : ℂ := if z = 0 then 1 else -1

lemma X7BL_10 : (1 : F2) ≠ 0 := by decide
lemma X7BL_11 : (1 : F2) + 1 = 0 := by decide
lemma X7BL_01 (z : F2) : z = 0 ∨ z = 1 := by revert z; decide

lemma X7BL_sgn_add (x y : F2) : X7BL_sgn (x + y) = X7BL_sgn x * X7BL_sgn y := by
  rcases X7BL_01 x with rfl | rfl <;> rcases X7BL_01 y with rfl | rfl <;> simp [X7BL_sgn, X7BL_10, X7BL_11]

lemma X7BL_sgn_sum {ι : Type*} (s : Finset ι) (f : ι → F2) :
    X7BL_sgn (∑ i ∈ s, f i) = ∏ i ∈ s, X7BL_sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [X7BL_sgn]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, X7BL_sgn_add, ih]

lemma X7BL_sgn_inj {x y : F2} (h : X7BL_sgn x = X7BL_sgn y) : x = y := by
  rcases X7BL_01 x with rfl | rfl <;> rcases X7BL_01 y with rfl | rfl <;> simp [X7BL_sgn, X7BL_10] at h ⊢ <;> norm_num at h

lemma X7BL_sgn_ne (x : F2) : X7BL_sgn x ≠ 0 := by
  unfold X7BL_sgn; split_ifs <;> norm_num

lemma X7BL_bit_inj {x y : Bool} (h : bit x = bit y) : x = y := by
  cases x <;> cases y <;> simp [bit] at h ⊢

def X7BL_unbit (z : F2) : Bool := decide (z = 1)

lemma X7BL_bit_unbit (z : F2) : bit (X7BL_unbit z) = z := by
  rcases X7BL_01 z with rfl | rfl <;> simp [bit, X7BL_unbit, X7BL_10.symm]

lemma X7BL_had (x y : Bool) : QAlgorithms.hadamard x y = ((Real.sqrt 2)⁻¹ : ℂ) * X7BL_sgn (bit x * bit y) := by
  cases x <;> cases y <;> simp [QAlgorithms.hadamard, X7BL_sgn, bit]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

lemma X7BL_ite (q : F2) [Decidable (q = 0)] : (if q = 0 then (1:ℂ) else -1) = X7BL_sgn q := by
  unfold X7BL_sgn; split_ifs <;> rfl

lemma X7BL_tensorH {I : Type*} [Fintype I] (b c : I → Bool) :
    tensorOps (fun _ : I => QAlgorithms.hadamard) b c =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card I * X7BL_sgn (∑ i, bit (b i) * bit (c i)) := by
  unfold tensorOps
  simp_rw [X7BL_had]
  rw [Finset.prod_mul_distrib, X7BL_sgn_sum]
  simp

lemma X7BL_formula {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I)
    (hB : IsUnit G.B.det) (a c : I → Bool) :
    bellNormalizer G a c = ((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card I *
      X7BL_sgn (quadratic G.AS a + ∑ i, (∑ j, G.B j i * bit (a j)) * bit (c i) +
        quadratic G.AN c) := by
  have hBT : IsUnit G.B.transpose.det := by rwa [Matrix.det_transpose]
  set M := (G.B.transpose)⁻¹ with hM
  have iff1 : ∀ b : I → Bool, ((fun i => bit (a i)) = M.mulVec (fun i => bit (b i))) ↔
      (fun i => bit (b i)) = G.B.transpose.mulVec (fun i => bit (a i)) := by
    intro b; constructor
    · intro h; rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hBT, Matrix.one_mulVec]
    · intro h; rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hBT, Matrix.one_mulVec]
  set bs : I → Bool := fun i => X7BL_unbit (G.B.transpose.mulVec (fun i => bit (a i)) i) with hbs
  have hbs' : (fun i => bit (bs i)) = G.B.transpose.mulVec (fun i => bit (a i)) := by
    funext i; simp [hbs, X7BL_bit_unbit]
  have uniq : ∀ b : I → Bool, (fun i => bit (b i)) = G.B.transpose.mulVec (fun i => bit (a i)) ↔
      b = bs := by
    intro b; constructor
    · intro h; funext i; apply X7BL_bit_inj; rw [← hbs'] at h; exact congrFun h i
    · rintro rfl; exact hbs'
  unfold bellNormalizer czLayer
  rw [Matrix.mul_diagonal, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single bs]
  · have hL : linearLayer M a bs = 1 := by
      unfold linearLayer; rw [if_pos ((iff1 bs).2 hbs')]
    have hbi : ∀ i, bit (bs i) = ∑ j, G.B j i * bit (a j) := fun i => by
      rw [congrFun hbs' i]; simp [Matrix.mulVec, dotProduct]
    rw [hL, X7BL_tensorH, X7BL_ite, X7BL_ite]
    simp_rw [hbi]
    rw [X7BL_sgn_add, X7BL_sgn_add]
    ring
  · intro b _ hb
    have : linearLayer M a b = 0 := by
      unfold linearLayer; rw [if_neg]
      intro h; exact hb ((uniq b).1 ((iff1 b).1 h))
    rw [this, zero_mul]
  · simp


def X7BL_fl {I : Type*} [DecidableEq I] (u : I) (x : I → Bool) : I → Bool :=
  Function.update x u (!x u)

lemma X7BL_bit_fl {I : Type*} [DecidableEq I] (u : I) (x : I → Bool) (k : I) :
    bit (X7BL_fl u x k) = bit (x k) + if k = u then 1 else 0 := by
  unfold X7BL_fl
  by_cases h : k = u
  · subst h; cases x k <;> simp [bit] <;> decide
  · simp [Function.update_apply, h]

lemma X7BL_bit_fl2 {I : Type*} [DecidableEq I] (u v : I) (huv : u ≠ v) (x : I → Bool) (k : I) :
    bit (X7BL_fl u (X7BL_fl v x) k) =
      bit (x k) + (if k = u then 1 else 0) + (if k = v then 1 else 0) := by
  rw [X7BL_bit_fl, X7BL_bit_fl]; ring

lemma X7BL_quad4 (p q r s t w : F2) :
    p*q + (p+r+t)*(q+s+w) + (p+r)*(q+s) + (p+t)*(q+w) = r*w + t*s := by
  revert p q r s t w; decide

lemma X7BL_term4 (C : Prop) [Decidable C] (A p q r s t w : F2) :
    ((if C then A * p * q else 0) + (if C then A * (p+r+t) * (q+s+w) else 0) +
      (if C then A * (p+r) * (q+s) else 0) + (if C then A * (p+t) * (q+w) else 0)) =
    (if C then A else 0) * (r*w + t*s) := by
  split_ifs
  · linear_combination A * X7BL_quad4 p q r s t w
  · simp

lemma X7BL_Q2 {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I F2)
    (hA : ∀ a b, A a b = A b a) (u v : I) (huv : u ≠ v) (x : I → Bool) :
    quadratic A x + quadratic A (X7BL_fl u (X7BL_fl v x)) + quadratic A (X7BL_fl u x) +
      quadratic A (X7BL_fl v x) = A u v := by
  unfold quadratic
  simp_rw [X7BL_bit_fl2 u v huv, X7BL_bit_fl]
  simp only [← Finset.sum_add_distrib]
  have term : ∀ a b : I,
      ((if (Fintype.equivFin I a).val < (Fintype.equivFin I b).val then
          A a b * bit (x a) * bit (x b) else 0) +
        (if (Fintype.equivFin I a).val < (Fintype.equivFin I b).val then
          A a b * (bit (x a) + (if a = u then 1 else 0) + (if a = v then 1 else 0)) *
            (bit (x b) + (if b = u then 1 else 0) + (if b = v then 1 else 0)) else 0) +
        (if (Fintype.equivFin I a).val < (Fintype.equivFin I b).val then
          A a b * (bit (x a) + (if a = u then 1 else 0)) * (bit (x b) + (if b = u then 1 else 0))
          else 0) +
        (if (Fintype.equivFin I a).val < (Fintype.equivFin I b).val then
          A a b * (bit (x a) + (if a = v then 1 else 0)) * (bit (x b) + (if b = v then 1 else 0))
          else 0)) =
      (if (Fintype.equivFin I a).val < (Fintype.equivFin I b).val then A a b else 0) *
        ((if a = u then 1 else 0) * (if b = v then 1 else 0) +
          (if a = v then 1 else 0) * (if b = u then 1 else 0)) := by
    intro a b
    exact X7BL_term4 _ _ _ _ _ _ _ _
  simp_rw [term, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hne : (Fintype.equivFin I u).val ≠ (Fintype.equivFin I v).val := by
    intro h; exact huv ((Fintype.equivFin I).injective (Fin.ext h))
  rcases lt_or_gt_of_ne hne with h | h
  · simp [h, not_lt_of_gt h]
  · simp [h, not_lt_of_gt h, hA v u]


def X7BL_beta {I : Type*} [Fintype I] (B : Matrix I I F2) (a c : I → Bool) : F2 :=
  ∑ i, (∑ j, B j i * bit (a j)) * bit (c i)

lemma X7BL_beta1 {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I F2) (u : I)
    (a c : I → Bool) :
    X7BL_beta B (X7BL_fl u a) c = X7BL_beta B a c + ∑ i, B u i * bit (c i) := by
  unfold X7BL_beta
  simp_rw [X7BL_bit_fl, mul_add, Finset.sum_add_distrib, add_mul, Finset.sum_add_distrib]
  simp [mul_ite]

lemma X7BL_beta2 {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I F2) (j : I)
    (a c : I → Bool) :
    X7BL_beta B a (X7BL_fl j c) = X7BL_beta B a c + ∑ k, B k j * bit (a k) := by
  unfold X7BL_beta
  simp_rw [X7BL_bit_fl, mul_add, Finset.sum_add_distrib]
  simp [mul_ite]

lemma X7BL_gamma {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I F2) (u j : I)
    (a : I → Bool) :
    ∑ k, B k j * bit (X7BL_fl u a k) = ∑ k, B k j * bit (a k) + B u j := by
  simp_rw [X7BL_bit_fl, mul_add, Finset.sum_add_distrib]
  simp [mul_ite]

def X7BL_Phi {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) (a c : I → Bool) : F2 :=
  quadratic G.AS a + X7BL_beta G.B a c + quadratic G.AN c

lemma X7BL_XA {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) (u v : I) (huv : u ≠ v)
    (a c : I → Bool) :
    X7BL_Phi G a c + X7BL_Phi G (X7BL_fl u (X7BL_fl v a)) c + X7BL_Phi G (X7BL_fl u a) c +
      X7BL_Phi G (X7BL_fl v a) c = G.AS u v := by
  have hq := X7BL_Q2 G.AS G.symS u v huv a
  unfold X7BL_Phi
  rw [X7BL_beta1, X7BL_beta1, X7BL_beta1]
  rw [← hq]
  have h2 : (2:F2) = 0 := by decide
  have h4 : (4:F2) = 0 := by decide
  ring_nf
  simp only [h2, h4, mul_zero, add_zero, zero_add]
  try ring

lemma X7BL_XC {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) (j l : I) (hjl : j ≠ l)
    (a c : I → Bool) :
    X7BL_Phi G a c + X7BL_Phi G a (X7BL_fl j (X7BL_fl l c)) + X7BL_Phi G a (X7BL_fl j c) +
      X7BL_Phi G a (X7BL_fl l c) = G.AN j l := by
  have hq := X7BL_Q2 G.AN G.symN j l hjl c
  unfold X7BL_Phi
  rw [X7BL_beta2, X7BL_beta2, X7BL_beta2]
  rw [← hq]
  have h2 : (2:F2) = 0 := by decide
  have h4 : (4:F2) = 0 := by decide
  ring_nf
  simp only [h2, h4, mul_zero, add_zero, zero_add]
  try ring

lemma X7BL_XX {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) (u j : I)
    (a c : I → Bool) :
    X7BL_Phi G a c + X7BL_Phi G (X7BL_fl u a) (X7BL_fl j c) + X7BL_Phi G (X7BL_fl u a) c +
      X7BL_Phi G a (X7BL_fl j c) = G.B u j := by
  unfold X7BL_Phi
  simp only [X7BL_beta1, X7BL_beta2, X7BL_gamma]
  have h2 : (2:F2) = 0 := by decide
  have h4 : (4:F2) = 0 := by decide
  ring_nf
  simp only [h2, h4, mul_zero, add_zero, zero_add]
  try ring


lemma X7BL_PA {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) (V : I → Op Bool)
    (u v : I) (huv : u ≠ v) (a c : I → Bool) :
    (∏ i, V i (a (e i)) (c i)) * (∏ i, V i (X7BL_fl u (X7BL_fl v a) (e i)) (c i)) =
      (∏ i, V i (X7BL_fl u a (e i)) (c i)) * (∏ i, V i (X7BL_fl v a (e i)) (c i)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold X7BL_fl
  by_cases h1 : e i = u
  · have h2 : e i ≠ v := h1 ▸ huv
    simp [Function.update_apply, h1, huv, Ne.symm huv]; ring
  · by_cases h2 : e i = v
    · simp [Function.update_apply, h1, h2, huv, Ne.symm huv]
    · simp [Function.update_apply, h1, h2]

lemma X7BL_PC {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) (V : I → Op Bool)
    (j l : I) (hjl : j ≠ l) (a c : I → Bool) :
    (∏ i, V i (a (e i)) (c i)) * (∏ i, V i (a (e i)) (X7BL_fl j (X7BL_fl l c) i)) =
      (∏ i, V i (a (e i)) (X7BL_fl j c i)) * (∏ i, V i (a (e i)) (X7BL_fl l c i)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold X7BL_fl
  by_cases h1 : i = j
  · subst h1
    simp [Function.update_apply, hjl]; ring
  · by_cases h2 : i = l
    · subst h2; simp [Function.update_apply, h1, Ne.symm hjl]
    · simp [Function.update_apply, h1, h2]

lemma X7BL_PX {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) (V : I → Op Bool)
    (u j : I) (huj : u ≠ e j) (a c : I → Bool) :
    (∏ i, V i (a (e i)) (c i)) * (∏ i, V i (X7BL_fl u a (e i)) (X7BL_fl j c i)) =
      (∏ i, V i (X7BL_fl u a (e i)) (c i)) * (∏ i, V i (a (e i)) (X7BL_fl j c i)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold X7BL_fl
  by_cases h1 : i = j
  · subst h1
    simp [Function.update_apply, Ne.symm huj]; try ring
  · by_cases h2 : e i = u
    · simp [Function.update_apply, h1, h2]; try ring
    · simp [Function.update_apply, h1, h2]

lemma X7BL_cross {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) (hB : IsUnit G.B.det)
    (a1 c1 a2 c2 a3 c3 a4 c4 : I → Bool)
    (h : bellNormalizer G a1 c1 * bellNormalizer G a2 c2 =
      bellNormalizer G a3 c3 * bellNormalizer G a4 c4) :
    X7BL_Phi G a1 c1 + X7BL_Phi G a2 c2 + X7BL_Phi G a3 c3 + X7BL_Phi G a4 c4 = 0 := by
  simp only [X7BL_formula G hB] at h
  have hk : ((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card I ≠ 0 := by
    apply pow_ne_zero; simp
  have h' : X7BL_sgn (X7BL_Phi G a1 c1 + X7BL_Phi G a2 c2) =
      X7BL_sgn (X7BL_Phi G a3 c3 + X7BL_Phi G a4 c4) := by
    rw [X7BL_sgn_add, X7BL_sgn_add]
    have : (((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card I) ^ 2 *
        (X7BL_sgn (X7BL_Phi G a1 c1) * X7BL_sgn (X7BL_Phi G a2 c2)) =
        (((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card I) ^ 2 *
        (X7BL_sgn (X7BL_Phi G a3 c3) * X7BL_sgn (X7BL_Phi G a4 c4)) := by
      unfold X7BL_Phi X7BL_beta; linear_combination h
    exact mul_left_cancel₀ (pow_ne_zero 2 hk) this
  have := X7BL_sgn_inj h'
  rw [add_assoc _ (X7BL_Phi G a3 c3), ← this]
  have h2 : ∀ z : F2, z + z = 0 := by decide
  rw [h2]

lemma X7BL_SC_had : SingleClifford QAlgorithms.hadamard := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs' : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, hs]; norm_num
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1/2 := by rw [sq, hs']
  have hH : QAlgorithms.hadamardᴴ = QAlgorithms.hadamard := by
    ext i j; cases i <;> cases j <;>
      simp [QAlgorithms.hadamard, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hH]
    ext i j; cases i <;> cases j <;>
      simp [QAlgorithms.hadamard, Matrix.mul_apply, hs'] <;> ring
  · intro ax
    rw [hH]
    cases ax
    · refine ⟨Axis.Z, 1, Or.inl rfl, ?_⟩
      ext i j; cases i <;> cases j <;>
        simp [axisMatrix, QAlgorithms.hadamard, QAlgorithms.pauliX, QAlgorithms.pauliZ,
          Matrix.mul_apply, hs'] <;> ring
    · refine ⟨Axis.Y, -1, Or.inr rfl, ?_⟩
      ext i j; cases i <;> cases j <;>
        simp [axisMatrix, QAlgorithms.hadamard, QAlgorithms.pauliY,
          Matrix.mul_apply] <;> ring_nf <;> (try rw [hsq]) <;> ring
    · refine ⟨Axis.X, 1, Or.inl rfl, ?_⟩
      ext i j; cases i <;> cases j <;>
        simp [axisMatrix, QAlgorithms.hadamard, QAlgorithms.pauliX, QAlgorithms.pauliZ,
          Matrix.mul_apply, hs'] <;> ring

end

end QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

open QAlgorithms.Papers.Independent.Information100.P22

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

theorem solution (nu : ℕ) (hnu : 1 ≤ nu) (G : CutGraph (Fin nu))
    (hB : IsUnit G.B.det) :
    LocalCliffordPermutation (bellNormalizer G) ↔
      G.AS = 0 ∧ G.AN = 0 ∧ BinaryPermutation G.B := by
  have h2 : ∀ z : F2, z + z = 0 := by decide
  constructor
  · rintro ⟨e, V, _, hU⟩
    let a0 : Fin nu → Bool := fun _ => false
    refine ⟨?_, ?_, ?_⟩
    · ext u v
      by_cases huv : u = v
      · subst huv; simpa using G.diagS u
      · have := X7BL_cross G hB a0 a0 (X7BL_fl u (X7BL_fl v a0)) a0 (X7BL_fl u a0) a0
          (X7BL_fl v a0) a0 (by simp only [hU]; exact X7BL_PA e V u v huv a0 a0)
        rw [X7BL_XA G u v huv] at this
        simpa using this
    · ext j l
      by_cases hjl : j = l
      · subst hjl; simpa using G.diagN j
      · have := X7BL_cross G hB a0 a0 a0 (X7BL_fl j (X7BL_fl l a0)) a0 (X7BL_fl j a0)
          a0 (X7BL_fl l a0) (by simp only [hU]; exact X7BL_PC e V j l hjl a0 a0)
        rw [X7BL_XC G j l hjl] at this
        simpa using this
    · have hz : ∀ u j, u ≠ e j → G.B u j = 0 := by
        intro u j huj
        have := X7BL_cross G hB a0 a0 (X7BL_fl u a0) (X7BL_fl j a0) (X7BL_fl u a0) a0
          a0 (X7BL_fl j a0) (by simp only [hU]; exact X7BL_PX e V u j huj a0 a0)
        rw [X7BL_XX G u j] at this
        exact this
      refine ⟨e, fun u j => ?_⟩
      split_ifs with h
      · subst h
        rcases X7BL_01 (G.B (e j) j) with h0 | h1
        · exfalso
          have hdet : G.B.det = 0 := Matrix.det_eq_zero_of_column_eq_zero j (fun i => by
            by_cases hi : i = e j
            · subst hi; exact h0
            · exact hz i j hi)
          rw [hdet] at hB; exact not_isUnit_zero hB
        · exact h1
      · exact hz u j h
  · rintro ⟨hS, hN, e, he⟩
    refine ⟨e, fun _ => QAlgorithms.hadamard, fun _ => X7BL_SC_had, fun a c => ?_⟩
    rw [X7BL_formula G hB, hS, hN]
    have hq : ∀ x : Fin nu → Bool, quadratic (0 : Matrix (Fin nu) (Fin nu) F2) x = 0 := by
      intro x; simp [quadratic]
    rw [hq, hq, zero_add, add_zero]
    have hb : ∀ i, (∑ j, G.B j i * bit (a j)) = bit (a (e i)) := by
      intro i; simp [he]
    simp_rw [hb]
    have := X7BL_tensorH (fun i => a (e i)) c
    unfold tensorOps at this
    rw [this]

end
