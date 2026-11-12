-- Prove2me | solution 1 for RetroCorr.Separation.q2_exceeds_holevo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T11:18:30.887198+00:00
-- url     : https://prove2.me/submissions/477eba0f-cda9-4d24-8388-084764ce69c0

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel
import Definitions.Def_RetroCorr_Separation_Holevo
import Definitions.Def_RetroCorr_Separation_TwoWay

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! Proof of RetroCorr.Separation.q2_exceeds_holevo.
Part A: an exact rate-1 two-way protocol, so Q2(R_{2,2}) >= 1.
Part B: C_H(R_{2,2}) <= 5/6 < 1 (entropy bounds, Pauli twirl on U_1, tetrahedral average on W). -/

/-! Child A work file for 86121560: the exact rate-1 protocol. -/

namespace RetroCorr.Separation.Draft86121560A
open RetroCorr.Separation MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise


lemma star_ite0 (P : Prop) [Decidable P] (z : ℂ) :
    star (if P then z else 0) = if P then star z else 0 := by
  split_ifs <;> simp

lemma haar_isProb (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma flagLaw_isProb : IsProbabilityMeasure (flagLaw 2 2) := by
  haveI := haar_isProb 2
  unfold flagLaw
  infer_instance

lemma conj_apply {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) (X : Matrix ι ι ℂ) (i k : κ) :
    (A * X * Aᴴ) i k = ∑ j, ∑ l, A i j * X j l * star (A k l) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma aliceBranch_apply {a b h : ℕ} (E : Matrix (Fin h) (Fin a) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (p p' : Fin h) (q q' : Fin b) :
    aliceBranch (b := b) E X (p, q) (p', q') =
      ∑ x, ∑ x', E p x * X (x, q) (x', q') * star (E p' x') := by
  rw [aliceBranch, QAlgorithms.conjSuperop, conj_apply]
  simp only [Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, star_ite0, star_one, star_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma bobBranch_apply {a b h : ℕ} (E : Matrix (Fin h) (Fin b) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (p p' : Fin a) (q q' : Fin h) :
    bobBranch (a := a) E X (p, q) (p', q') =
      ∑ y, ∑ y', E q y * X (p, y) (p', y') * star (E q' y') := by
  rw [bobBranch, QAlgorithms.conjSuperop, conj_apply]
  simp only [Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul, star_ite0, star_one, star_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- One branch of the channel in closed form. -/
lemma retroBranch_apply (k : Flag 2 2) (Z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (o o' : Fin 2) :
    retroBranch 2 2 k Z o o' = ∑ j, ∑ d, ∑ d', ∑ c, ∑ c',
      (k.2 j : Matrix (Fin 2) (Fin 2) ℂ) o d * ((k.1 : Matrix (Fin 2) (Fin 2) ℂ) c j *
        star ((k.1 : Matrix (Fin 2) (Fin 2) ℂ) c' j) * Z (c', d) (c, d')) *
        star ((k.2 j : Matrix (Fin 2) (Fin 2) ℂ) o' d') := by
  simp only [retroBranch, Matrix.sum_apply, conj_apply, QAlgorithms.traceLeft, Matrix.of_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, basisProj, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

lemma unit_col {n : ℕ} (W : Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) :
    ∑ l, star ((W : Matrix (Fin n) (Fin n) ℂ) l i) * (W : Matrix (Fin n) (Fin n) ℂ) l j =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp W.2) i) j
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h

/-- `1/√2`. -/
noncomputable def c0 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma c0_sq : c0 * star c0 = (1 / 2 : ℂ) := by
  simp only [c0, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

section Stage
variable {a a' b : ℕ} (α : Fin a ≃ Fin 2 × Fin a')

/-- Alice's memory after the preparation: (ref, rest) kept, (control, data) sent. -/
def eA (a' : ℕ) : Fin ((2 * a') * (2 * 2)) ≃ Fin (2 * a') × (Fin 2 × Fin 2) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

def βA (a' : ℕ) : Fin (2 * a') ≃ Fin 2 × Fin a' := finProdFinEquiv.symm

def fB (b : ℕ) : Fin (2 * b) ≃ Fin 2 × Fin b := finProdFinEquiv.symm

/-- Preparation isometry: append the ebit on (ref, control); move the data qubit to the send slot. -/
noncomputable def E0 : Matrix (Fin ((2 * a') * (2 * 2))) (Fin a) ℂ := fun p x =>
  if x = α.symm ((eA a' p).2.2, (βA a' (eA a' p).1).2) then
    (if (eA a' p).2.1 = (βA a' (eA a' p).1).1 then c0 else 0) else 0

lemma prep_apply (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ κ' : Fin (2 * a'))
    (c d c' d' : Fin 2) (q q' : Fin b) :
    aliceBranch (b := b) (E0 α) X ((eA a').symm (κ, (c, d)), q) ((eA a').symm (κ', (c', d')), q') =
      if c = (βA a' κ).1 ∧ c' = (βA a' κ').1 then
        (c0 * star c0) * X (α.symm (d, (βA a' κ).2), q) (α.symm (d', (βA a' κ').2), q') else 0 := by
  rw [aliceBranch_apply]
  simp only [E0, Equiv.apply_symm_apply, ite_mul, zero_mul, star_ite0, star_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mem_univ, if_true]
  by_cases h1 : c = (βA a' κ).1 <;> by_cases h2 : c' = (βA a' κ').1 <;> simp [h1, h2] <;> ring

/-- After preparation and one channel use with flag `(W, U)`. -/
lemma send_apply (W : Matrix.unitaryGroup (Fin 2) ℂ) (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ κ' : Fin (2 * a')) (y y' : Fin (2 * b)) :
    sendVia (eA a') (fB b) (retroBranch 2 2 (W, U)) (aliceBranch (b := b) (E0 α) X) (κ, y) (κ', y') =
      (c0 * star c0) * ∑ j, (W : Matrix (Fin 2) (Fin 2) ℂ) (βA a' κ').1 j *
        star ((W : Matrix (Fin 2) (Fin 2) ℂ) (βA a' κ).1 j) *
        ∑ d, ∑ d', (U j : Matrix (Fin 2) (Fin 2) ℂ) (fB b y).1 d *
          X (α.symm (d, (βA a' κ).2), (fB b y).2) (α.symm (d', (βA a' κ').2), (fB b y').2) *
          star ((U j : Matrix (Fin 2) (Fin 2) ℂ) (fB b y').1 d') := by
  simp only [sendVia, retroBranch_apply, Matrix.of_apply, prep_apply, mul_ite, mul_zero,
    ite_and, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  refine Finset.sum_congr rfl fun d' _ => ?_
  ring

/-- Alice's measurement of her reference in the basis `B^T` (outcome `j`), keeping the rest. -/
noncomputable def Ej (W : Matrix.unitaryGroup (Fin 2) ℂ) (j : Fin 2) :
    Matrix (Fin a') (Fin (2 * a')) ℂ := fun r κ =>
  if (βA a' κ).2 = r then (W : Matrix (Fin 2) (Fin 2) ℂ) (βA a' κ).1 j else 0

/-- Bob's correction `U_j^†` on the received data qubit. -/
noncomputable def Bj (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ) (j : Fin 2) :
    Matrix (Fin (2 * b)) (Fin (2 * b)) ℂ := fun pb pb'' =>
  if (fB b pb).2 = (fB b pb'').2 then
    star ((U j : Matrix (Fin 2) (Fin 2) ℂ) (fB b pb'').1 (fB b pb).1) else 0

lemma meas_apply {c : ℕ} (W : Matrix.unitaryGroup (Fin 2) ℂ) (j : Fin 2)
    (T : Matrix (Fin (2 * a') × Fin c) (Fin (2 * a') × Fin c) ℂ) (r r' : Fin a') (y y' : Fin c) :
    aliceBranch (b := c) (Ej (a' := a') W j) T (r, y) (r', y') =
      ∑ ref, ∑ ref', (W : Matrix (Fin 2) (Fin 2) ℂ) ref j *
        T ((βA a').symm (ref, r), y) ((βA a').symm (ref', r'), y') *
        star ((W : Matrix (Fin 2) (Fin 2) ℂ) ref' j) := by
  rw [aliceBranch_apply, ← (βA a').symm.sum_comp]
  conv_lhs => arg 2; ext z; rw [← (βA a').symm.sum_comp]
  simp only [Ej, Equiv.apply_symm_apply, Fintype.sum_prod_type, ite_mul, mul_ite, zero_mul, mul_zero,
    star_ite0, star_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.mem_univ, if_true]

lemma bob_apply (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ) (j : Fin 2)
    (Y : Matrix (Fin a' × Fin (2 * b)) (Fin a' × Fin (2 * b)) ℂ) (r r' : Fin a') (pb pb' : Fin (2 * b)) :
    bobBranch (a := a') (Bj (b := b) U j) Y (r, pb) (r', pb') =
      ∑ o, ∑ o', star ((U j : Matrix (Fin 2) (Fin 2) ℂ) o (fB b pb).1) *
        Y (r, (fB b).symm (o, (fB b pb).2)) (r', (fB b).symm (o', (fB b pb').2)) *
        (U j : Matrix (Fin 2) (Fin 2) ℂ) o' (fB b pb').1 := by
  rw [bobBranch_apply, ← (fB b).symm.sum_comp]
  conv_lhs => arg 2; ext z; rw [← (fB b).symm.sum_comp]
  simp only [Bj, Equiv.apply_symm_apply, Fintype.sum_prod_type, ite_mul, mul_ite, zero_mul, mul_zero,
    star_ite0, star_zero, star_star, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.mem_univ, if_true]

end Stage

lemma meas_collapse (W : Matrix.unitaryGroup (Fin 2) ℂ) (K : ℂ) (S : Fin 2 → ℂ) (j : Fin 2) :
    ∑ ref, ∑ ref', (W : Matrix (Fin 2) (Fin 2) ℂ) ref j *
      (K * ∑ j', (W : Matrix (Fin 2) (Fin 2) ℂ) ref' j' * star ((W : Matrix (Fin 2) (Fin 2) ℂ) ref j') * S j') *
      star ((W : Matrix (Fin 2) (Fin 2) ℂ) ref' j) = K * S j := by
  have h : ∑ ref, ∑ ref', (W : Matrix (Fin 2) (Fin 2) ℂ) ref j *
      (K * ∑ j', (W : Matrix (Fin 2) (Fin 2) ℂ) ref' j' * star ((W : Matrix (Fin 2) (Fin 2) ℂ) ref j') * S j') *
      star ((W : Matrix (Fin 2) (Fin 2) ℂ) ref' j) =
      K * ∑ j', (∑ ref, star ((W : Matrix (Fin 2) (Fin 2) ℂ) ref j') * (W : Matrix (Fin 2) (Fin 2) ℂ) ref j) *
        (∑ ref', star ((W : Matrix (Fin 2) (Fin 2) ℂ) ref' j) * (W : Matrix (Fin 2) (Fin 2) ℂ) ref' j') * S j' := by
    simp only [Fin.sum_univ_two]; ring
  rw [h]
  simp only [unit_col, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma bob_collapse (V : Matrix.unitaryGroup (Fin 2) ℂ) (K : ℂ) (F : Fin 2 → Fin 2 → ℂ) (p1 p1' : Fin 2) :
    ∑ o, ∑ o', star ((V : Matrix (Fin 2) (Fin 2) ℂ) o p1) *
      (K * ∑ d, ∑ d', (V : Matrix (Fin 2) (Fin 2) ℂ) o d * F d d' * star ((V : Matrix (Fin 2) (Fin 2) ℂ) o' d')) *
      (V : Matrix (Fin 2) (Fin 2) ℂ) o' p1' = K * F p1 p1' := by
  have h : ∑ o, ∑ o', star ((V : Matrix (Fin 2) (Fin 2) ℂ) o p1) *
      (K * ∑ d, ∑ d', (V : Matrix (Fin 2) (Fin 2) ℂ) o d * F d d' * star ((V : Matrix (Fin 2) (Fin 2) ℂ) o' d')) *
      (V : Matrix (Fin 2) (Fin 2) ℂ) o' p1' =
      K * ∑ d, ∑ d', (∑ o, star ((V : Matrix (Fin 2) (Fin 2) ℂ) o p1) * (V : Matrix (Fin 2) (Fin 2) ℂ) o d) *
        (∑ o', star ((V : Matrix (Fin 2) (Fin 2) ℂ) o' d') * (V : Matrix (Fin 2) (Fin 2) ℂ) o' p1') * F d d' := by
    simp only [Fin.sum_univ_two]; ring
  rw [h]
  simp only [unit_col, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mem_univ, if_true]

/-- KEY: for every flag, the stage (prep, send, measure reference, correct) moves Alice's data
qubit to Bob exactly. -/
lemma stage_key {a a' b : ℕ} (α : Fin a ≃ Fin 2 × Fin a') (W : Matrix.unitaryGroup (Fin 2) ℂ)
    (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    ∑ j : Fin 2, bobBranch (a := a') (Bj (b := b) U j) (aliceBranch (b := 2 * b) (Ej (a' := a') W j)
      (sendVia (eA a') (fB b) (retroBranch 2 2 (W, U)) (aliceBranch (b := b) (E0 α) X))) =
      X.submatrix (fun z : Fin a' × Fin (2 * b) => (α.symm ((fB b z.2).1, z.1), (fB b z.2).2))
        (fun z : Fin a' × Fin (2 * b) => (α.symm ((fB b z.2).1, z.1), (fB b z.2).2)) := by
  ext ⟨r, pb⟩ ⟨r', pb'⟩
  simp only [Matrix.sum_apply, bob_apply, meas_apply, send_apply, Equiv.apply_symm_apply]
  simp only [meas_collapse]
  simp only [bob_collapse (F := fun d d' => X (α.symm (d, r), (fB b pb).2) (α.symm (d', r'), (fB b pb').2))]
  rw [c0_sq]
  simp [Fin.sum_univ_two, Matrix.submatrix_apply]

lemma unit_row {n : ℕ} (W : Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) :
    ∑ l, (W : Matrix (Fin n) (Fin n) ℂ) i l * star ((W : Matrix (Fin n) (Fin n) ℂ) j l) =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp W.2) i) j
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h

lemma e0_kraus {a a' : ℕ} (α : Fin a ≃ Fin 2 × Fin a') :
    QAlgorithms.IsKrausFamily (fun _ : Fin 1 => E0 α) := by
  unfold QAlgorithms.IsKrausFamily
  ext x y
  rw [Fin.sum_univ_one, Matrix.mul_apply, ← (eA a').symm.sum_comp, Fintype.sum_prod_type,
    ← (βA a').symm.sum_comp, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, E0, Equiv.apply_symm_apply, Fintype.sum_prod_type,
    Equiv.eq_symm_apply, Prod.ext_iff, star_ite0, star_zero, ite_mul, mul_ite, zero_mul, mul_zero,
    ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  by_cases hxy : x = y
  · subst hxy
    simp only [and_self, if_true, Fin.sum_univ_two]
    rw [mul_comm (star c0), c0_sq]; norm_num
  · have : ¬ ((α y).1 = (α x).1 ∧ (α y).2 = (α x).2) := by
      rw [← Prod.ext_iff]; exact fun h => hxy (α.injective h).symm
    simp [hxy]
    intro h1 h2
    exact absurd ⟨h1.symm, h2.symm⟩ this

lemma ej_kraus {a' : ℕ} (W : Matrix.unitaryGroup (Fin 2) ℂ) :
    QAlgorithms.IsKrausFamily (fun j : Fin 2 => Ej (a' := a') W j) := by
  unfold QAlgorithms.IsKrausFamily
  have key : ∀ i i' : Fin 2, ∑ j, star ((W : Matrix (Fin 2) (Fin 2) ℂ) i j) *
      (W : Matrix (Fin 2) (Fin 2) ℂ) i' j = if i' = i then 1 else 0 := fun i i' => by
    rw [← unit_row W i' i]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  ext κ κ'
  obtain ⟨⟨i, r⟩, rfl⟩ := (βA a').symm.surjective κ
  obtain ⟨⟨i', r'⟩, rfl⟩ := (βA a').symm.surjective κ'
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Ej, Equiv.apply_symm_apply, star_ite0,
    star_zero, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mem_univ, if_true,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  rcases eq_or_ne r r' with rfl | hr
  · have h := key i i'
    rw [Fin.sum_univ_two] at h
    simp only [eq_comm (a := i')] at h
    simpa using h
  · simp [hr, Ne.symm hr]

lemma bj_kraus {b : ℕ} (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ) (j : Fin 2) :
    QAlgorithms.IsKrausFamily (fun _ : Fin 1 => Bj (b := b) U j) := by
  unfold QAlgorithms.IsKrausFamily
  ext x y
  rw [Fin.sum_univ_one, Matrix.mul_apply, ← (fB b).symm.sum_comp, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, Bj, Equiv.apply_symm_apply, Fintype.sum_prod_type,
    star_ite0, star_zero, star_star, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  rw [unit_row]
  by_cases h : x = y
  · subst h; simp
  · simp only [h, if_false]
    split_ifs with h1 h2
    · exact absurd ((fB b).injective (Prod.ext h2 h1.symm)) h
    · rfl
    · rfl

/-- One stage of the protocol as an `Adaptive` step. -/
lemma stage_adaptive {m n a a' b : ℕ} (α : Fin a ≃ Fin 2 × Fin a')
    (G : QAlgorithms.Superop (Fin a' × Fin (2 * b)) (QAlgorithms.Qubits m))
    (hadd : ∀ Y Z, G (Y + Z) = G Y + G Z)
    (hG : Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := n) G) :
    Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := n + 1)
      (fun X => G (X.submatrix
        (fun z : Fin a' × Fin (2 * b) => (α.symm ((fB b z.2).1, z.1), (fB b z.2).2))
        (fun z : Fin a' × Fin (2 * b) => (α.symm ((fB b z.2).1, z.1), (fB b z.2).2)))) := by
  haveI := flagLaw_isProb
  have hB : ∀ (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ) (j : Fin 2),
      Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := n)
        (fun Y => ∑ i : Fin 1, (fun _ : Fin 1 => G) i
          (bobBranch (a := a') ((fun _ : Fin 1 => Bj (b := b) U j) i) Y)) :=
    fun U j => Adaptive.bob (fun _ : Fin 1 => Bj (b := b) U j) (bj_kraus U j) (fun _ => G) (fun _ => hG)
  have hA : ∀ k : Flag 2 2, Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := n)
      (fun Z => ∑ j : Fin 2, (fun j : Fin 2 => fun Y => ∑ i : Fin 1, (fun _ : Fin 1 => G) i
          (bobBranch (a := a') ((fun _ : Fin 1 => Bj (b := b) k.2 j) i) Y)) j
        (aliceBranch (b := 2 * b) ((fun j => Ej (a' := a') k.1 j) j) Z)) :=
    fun k => Adaptive.alice (fun j => Ej (a' := a') k.1 j) (ej_kraus k.1) _ (fun j => hB k.2 j)
  have hS := Adaptive.send (eA a') (fB b) _ hA
  have hP := Adaptive.alice (b := b) (fun _ : Fin 1 => E0 α) (e0_kraus α) _ (fun _ => hS)
  convert hP using 1
  funext X
  have hk : ∀ k : Flag 2 2, ∑ j : Fin 2, ∑ i : Fin 1, G (bobBranch (a := a') (Bj (b := b) k.2 j)
      (aliceBranch (b := 2 * b) (Ej (a' := a') k.1 j)
        (sendVia (eA a') (fB b) (retroBranch 2 2 k) (aliceBranch (b := b) (E0 α) X)))) =
      G (X.submatrix
        (fun z : Fin a' × Fin (2 * b) => (α.symm ((fB b z.2).1, z.1), (fB b z.2).2))
        (fun z : Fin a' × Fin (2 * b) => (α.symm ((fB b z.2).1, z.1), (fB b z.2).2))) := by
    intro k
    rw [← stage_key α k.1 k.2 X]
    simp only [Fin.sum_univ_one, Fin.sum_univ_two, Prod.mk.eta, hadd]
  simp only [Fin.sum_univ_one] at hk ⊢
  simp only [hk]
  rw [integral_const]
  simp

lemma reindex_channel {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι]
    [DecidableEq κ] (τ : ι ≃ κ) (D : QAlgorithms.Superop κ ν) (hD : QAlgorithms.IsChannel D) :
    QAlgorithms.IsChannel (fun Y : Matrix ι ι ℂ => D (Y.submatrix τ.symm τ.symm)) := by
  obtain ⟨r, E, hE, hDE⟩ := hD
  refine ⟨r, fun i => (E i).submatrix id τ, ?_, fun Y => ?_⟩
  · unfold QAlgorithms.IsKrausFamily at hE ⊢
    have h2 : ∀ i, ((E i).submatrix id τ)ᴴ * (E i).submatrix id τ = ((E i)ᴴ * E i).submatrix τ τ := by
      intro i
      rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    simp only [h2]
    rw [show (∑ i, ((E i)ᴴ * E i).submatrix τ τ) = (∑ i, (E i)ᴴ * E i).submatrix τ τ by
      ext; simp [Matrix.sum_apply], hE, Matrix.submatrix_one_equiv]
  · show D (Y.submatrix τ.symm τ.symm) = _
    rw [hDE]
    unfold QAlgorithms.krausApply
    refine Finset.sum_congr rfl fun i _ => ?_
    ext o o'
    rw [conj_apply, conj_apply, ← τ.sum_comp]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← τ.sum_comp]
    simp [Matrix.submatrix_apply]

lemma channel_add {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (D : QAlgorithms.Superop ι κ)
    (hD : QAlgorithms.IsChannel D) (Y Z : Matrix ι ι ℂ) : D (Y + Z) = D Y + D Z := by
  obtain ⟨r, E, -, hDE⟩ := hD
  simp only [hDE, QAlgorithms.krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

/-- The whole protocol: `s` stages then Bob's reindexing decoder. -/
lemma run_adaptive (m : ℕ) : ∀ (s a b c : ℕ) (σ : Fin a × Fin b ≃ Fin c), a = 2 ^ s →
    ∀ D : QAlgorithms.Superop (Fin c) (QAlgorithms.Qubits m), QAlgorithms.IsChannel D →
      Adaptive (flagLaw 2 2) (retroBranch 2 2) m (n := s) (fun X => D (X.submatrix σ.symm σ.symm)) := by
  intro s
  induction s with
  | zero =>
    intro a b c σ ha D hD
    have ha' : a = 1 := by simpa using ha
    subst ha'
    let τ : Fin b ≃ Fin c := (Equiv.uniqueProd (Fin b) (Fin 1)).symm.trans σ
    have h := Adaptive.finish (μ := flagLaw 2 2) (N := retroBranch 2 2) (a := 1) (b := b)
      (fun Y => D (Y.submatrix τ.symm τ.symm)) (reindex_channel τ D hD)
    convert h using 1
    funext X
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, QAlgorithms.traceLeft, Matrix.of_apply]
    rw [Fintype.sum_unique]
    congr 1 <;> exact Prod.ext (Subsingleton.elim _ _) rfl
  | succ s ih =>
    intro a b c σ ha D hD
    let α : Fin a ≃ Fin 2 × Fin (2 ^ s) := (finCongr (ha.trans (pow_succ' 2 s))).trans finProdFinEquiv.symm
    let mvE : Fin (2 ^ s) × Fin (2 * b) ≃ Fin a × Fin b :=
      ((Equiv.prodCongr (Equiv.refl _) (fB b)).trans (Equiv.prodAssoc _ _ _).symm).trans
        (Equiv.prodCongr ((Equiv.prodComm _ _).trans α.symm) (Equiv.refl _))
    have hmv : (fun z : Fin (2 ^ s) × Fin (2 * b) => (α.symm ((fB b z.2).1, z.1), (fB b z.2).2)) = ⇑mvE := by
      funext z; rfl
    have hG := ih (2 ^ s) (2 * b) c (mvE.trans σ) rfl D hD
    have hst := stage_adaptive α _ (fun Y Z => by
      simp only [Matrix.submatrix_add]; exact channel_add D hD _ _) hG
    rw [hmv] at hst
    convert hst using 1
    funext X
    congr 1
    ext i j
    simp [Matrix.submatrix_apply]

lemma id_channel {ι : Type*} [Fintype ι] [DecidableEq ι] :
    QAlgorithms.IsChannel (fun Y : Matrix ι ι ℂ => Y) :=
  ⟨1, fun _ => 1, by simp [QAlgorithms.IsKrausFamily], fun ρ => by simp [QAlgorithms.krausApply]⟩

lemma pure_fid {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) (hψ : QAlgorithms.IsState ψ) :
    QAlgorithms.effectProb (QAlgorithms.pureDensity ψ) (QAlgorithms.pureDensity ψ) = 1 := by
  unfold QAlgorithms.effectProb QAlgorithms.pureDensity
  unfold QAlgorithms.IsState at hψ
  have hn : ∑ i, ψ i * (starRingEnd ℂ) (ψ i) = 1 := by
    have h2 : ‖ψ‖ ^ 2 = 1 := by rw [hψ]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    have : ∑ i, ψ i * (starRingEnd ℂ) (ψ i) = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [this, h2]; simp
  have ht : ((Matrix.of fun a b => ψ a * (starRingEnd ℂ) (ψ b)) *
      (Matrix.of fun a b => ψ a * (starRingEnd ℂ) (ψ b))).trace =
      (∑ i, ψ i * (starRingEnd ℂ) (ψ i)) * (∑ i, ψ i * (starRingEnd ℂ) (ψ i)) := by
    rw [Matrix.trace, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [ht, hn]; simp

/-- Child A: rate 1 is achievable with two-way classical communication (exact protocol). -/
theorem childA_proof : TwoWayAchievable (flagLaw 2 2) (retroBranch 2 2) 1 := by
  intro η hη
  refine ⟨0, fun n _ => ⟨n, by simp, ?_⟩⟩
  let ε : QAlgorithms.Qubits n ≃ Fin (2 ^ n) :=
    Fintype.equivFinOfCardEq (by simp [QAlgorithms.Qubits])
  let σ : Fin (2 ^ n) × Fin 1 ≃ Fin (2 ^ n) := Equiv.prodUnique _ _
  have henc := reindex_channel ε (fun Y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ => Y) id_channel
  have hdec := reindex_channel ε.symm (fun Y : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ => Y)
    id_channel
  refine ⟨⟨2 ^ n, _, henc, _, run_adaptive n n (2 ^ n) 1 (2 ^ n) σ rfl _ hdec⟩, ?_⟩
  intro ψ hψ
  have hout : ∀ ρ : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ,
      ((Matrix.kronecker (ρ.submatrix ε.symm ε.symm) (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
        σ.symm σ.symm).submatrix ε.symm.symm ε.symm.symm = ρ := by
    intro ρ
    ext i j
    simp [σ, Matrix.kronecker, Matrix.kroneckerMap_apply]
  show 1 - η ≤ QAlgorithms.effectProb _ (((Matrix.kronecker
    ((QAlgorithms.pureDensity ψ).submatrix ε.symm ε.symm) (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
        σ.symm σ.symm).submatrix ε.symm.symm ε.symm.symm)
  rw [hout, pure_fid ψ hψ]
  linarith

end RetroCorr.Separation.Draft86121560A

/-! Child B for 86121560: C_H(R_{2,2}) <= 5/6 (bits). Pointwise: Holevo integrand <= sum_x p_x Tr (N_k rho_x)^2
using S(s) >= 1 - Tr s^2 (any dimension) and S <= 1 (qubit). -/

namespace RetroCorr.Separation.Draft86121560B
open RetroCorr.Separation MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder

/-! ### B1: entropy bounds via eigenvalues -/

lemma trace_cfc_herm {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]
  first
    | rw [Unitary.coe_star_mul_self]
    | rw [Unitary.star_mul_self]
    | rw [Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2]
  rw [Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma entropy_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    QAlgorithms.vnEntropy s = ∑ i, -(hs.eigenvalues i * Real.logb 2 (hs.eigenvalues i)) := by
  rw [QAlgorithms.vnEntropy, trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [Finset.sum_neg_distrib]

lemma purity_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    (s * s).trace.re = ∑ i, hs.eigenvalues i * hs.eigenvalues i := by
  have hsa : IsSelfAdjoint s := hs
  have h1 : cfc (fun x : ℝ => x * x) s = s * s := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) s, cfc_id' ℝ s hsa]
  rw [← h1, trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]

lemma eig_facts {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ}
    (hs : QAlgorithms.IsDensityMatrix s) :
    (∀ i, 0 ≤ hs.1.1.eigenvalues i) ∧ ∑ i, hs.1.1.eigenvalues i = 1 := by
  refine ⟨fun i => hs.1.eigenvalues_nonneg i, ?_⟩
  have h := hs.1.1.trace_eq_sum_eigenvalues
  have h2 : ((∑ j, hs.1.1.eigenvalues j : ℝ) : ℂ) = 1 := by
    push_cast
    exact h.symm.trans hs.2
  exact_mod_cast h2

lemma log_two_lt_one : Real.log 2 < 1 := by
  have := Real.log_two_lt_d9
  linarith

lemma negMulLogb_ge (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x - x * x ≤ -(x * Real.logb 2 x) := by
  rcases h0.lt_or_eq with hx | hx
  · have hL : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
    have hL0 : Real.log x ≤ 0 := Real.log_nonpos h0 h1
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 := log_two_lt_one
    rw [Real.logb, show -(x * (Real.log x / Real.log 2)) = (x * -Real.log x) / Real.log 2 by ring,
      le_div_iff₀ h2]
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - x ≤ -Real.log x by linarith) h0,
      mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - x)) (by linarith : 0 ≤ 1 - Real.log 2)]
  · subst hx
    simp

lemma negMulLogb_le (x : ℝ) (h0 : 0 ≤ x) :
    -(x * Real.logb 2 x) ≤ (x * Real.log 2 + 1 / 2 - x) / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, show -(x * (Real.log x / Real.log 2)) = (-(x * Real.log x)) / Real.log 2 by ring]
  apply div_le_div_of_nonneg_right _ h2.le
  rcases h0.lt_or_eq with hx | hx
  · have h := Real.one_sub_inv_le_log_of_pos (by positivity : (0 : ℝ) < 2 * x)
    rw [Real.log_mul two_ne_zero hx.ne'] at h
    have h5 : x * (1 - (2 * x)⁻¹) = x - 1 / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h hx.le]
  · subst hx
    simp

theorem entropy_ge {n : Type*} [Fintype n] [DecidableEq n] (s : Matrix n n ℂ)
    (hs : QAlgorithms.IsDensityMatrix s) : 1 - (s * s).trace.re ≤ QAlgorithms.vnEntropy s := by
  obtain ⟨hnn, hsum⟩ := eig_facts hs
  rw [entropy_eig hs.1.1, purity_eig hs.1.1]
  have hle : ∀ i, hs.1.1.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  rw [show (1 : ℝ) - ∑ i, hs.1.1.eigenvalues i * hs.1.1.eigenvalues i =
      ∑ i, (hs.1.1.eigenvalues i - hs.1.1.eigenvalues i * hs.1.1.eigenvalues i) by
    rw [Finset.sum_sub_distrib, hsum]]
  exact Finset.sum_le_sum fun i _ => negMulLogb_ge _ (hnn i) (hle i)

theorem entropy_le_one (s : Matrix (Fin 2) (Fin 2) ℂ) (hs : QAlgorithms.IsDensityMatrix s) :
    QAlgorithms.vnEntropy s ≤ 1 := by
  obtain ⟨hnn, hsum⟩ := eig_facts hs
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [entropy_eig hs.1.1]
  calc ∑ i, -(hs.1.1.eigenvalues i * Real.logb 2 (hs.1.1.eigenvalues i))
      ≤ ∑ i, (hs.1.1.eigenvalues i * Real.log 2 + 1 / 2 - hs.1.1.eigenvalues i) / Real.log 2 :=
        Finset.sum_le_sum fun i _ => negMulLogb_le _ (hnn i)
    _ = 1 := by
      rw [Fin.sum_univ_two] at hsum ⊢
      rw [← add_div, div_eq_one_iff_eq h2.ne']
      linear_combination (Real.log 2 - 1) * hsum

/-! ### Output of R_{2,2} is a density matrix (Kraus form) -/

lemma conj_apply {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) (X : Matrix ι ι ℂ) (i k : κ) :
    (A * X * Aᴴ) i k = ∑ j, ∑ l, A i j * X j l * star (A k l) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma retroBranch_apply (k : Flag 2 2) (Z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (o o' : Fin 2) :
    retroBranch 2 2 k Z o o' = ∑ j, ∑ d, ∑ d', ∑ c, ∑ c',
      (k.2 j : Matrix (Fin 2) (Fin 2) ℂ) o d * ((k.1 : Matrix (Fin 2) (Fin 2) ℂ) c j *
        star ((k.1 : Matrix (Fin 2) (Fin 2) ℂ) c' j) * Z (c', d) (c, d')) *
        star ((k.2 j : Matrix (Fin 2) (Fin 2) ℂ) o' d') := by
  simp only [retroBranch, Matrix.sum_apply, conj_apply, QAlgorithms.traceLeft, Matrix.of_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, basisProj, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

lemma unit_col {n : ℕ} (W : Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) :
    ∑ l, star ((W : Matrix (Fin n) (Fin n) ℂ) l i) * (W : Matrix (Fin n) (Fin n) ℂ) l j =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp W.2) i) j
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h

lemma unit_row {n : ℕ} (W : Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) :
    ∑ l, (W : Matrix (Fin n) (Fin n) ℂ) i l * star ((W : Matrix (Fin n) (Fin n) ℂ) j l) =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp W.2) i) j
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h

/-- Kraus operator `K_j = U_j (⟨w̄_j| ⊗ I)` of `R_{2,2}` at flag `k`. -/
noncomputable def K (k : Flag 2 2) (j : Fin 2) : Matrix (Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun o cd => star ((k.1 : Matrix (Fin 2) (Fin 2) ℂ) cd.1 j) *
    (k.2 j : Matrix (Fin 2) (Fin 2) ℂ) o cd.2

lemma retro_kraus_form (k : Flag 2 2) (Z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    retroBranch 2 2 k Z = ∑ j, K k j * Z * (K k j)ᴴ := by
  ext o o'
  rw [retroBranch_apply, Matrix.sum_apply]
  simp only [conj_apply, K, Matrix.of_apply, Fintype.sum_prod_type, star_mul', star_star]
  simp only [Fin.sum_univ_two]
  ring

lemma kraus_complete (k : Flag 2 2) : ∑ j, (K k j)ᴴ * K k j = 1 := by
  ext ⟨c, d⟩ ⟨c', d'⟩
  have key : ∀ j, ∑ o, star (K k j o (c, d)) * K k j o (c', d') =
      (k.1 : Matrix (Fin 2) (Fin 2) ℂ) c j * star ((k.1 : Matrix (Fin 2) (Fin 2) ℂ) c' j) *
        (if d = d' then 1 else 0) := by
    intro j
    rw [← unit_col (k.2 j) d d', Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [K, Matrix.of_apply, star_mul', star_star]
    ring
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  simp only [key]
  rw [← Finset.sum_mul, unit_row]
  by_cases h1 : c = c' <;> by_cases h2 : d = d' <;> simp [h1, h2]

lemma psd_sum {ι n : Type*} [Fintype n] (s : Finset ι) (f : ι → Matrix n n ℂ)
    (h : ∀ i, (f i).PosSemidef) : (∑ i ∈ s, f i).PosSemidef :=
  Finset.sum_induction f (fun M => M.PosSemidef) (fun _ _ ha hb => ha.add hb)
    Matrix.PosSemidef.zero (fun i _ => h i)

theorem retro_density (k : Flag 2 2) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) : QAlgorithms.IsDensityMatrix (retroBranch 2 2 k ρ) := by
  rw [retro_kraus_form]
  refine ⟨psd_sum _ _ fun j => hρ.1.mul_mul_conjTranspose_same (K k j), ?_⟩
  calc (∑ j, K k j * ρ * (K k j)ᴴ).trace = ∑ j, ((K k j)ᴴ * K k j * ρ).trace := by
        rw [Matrix.trace_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ((∑ j, (K k j)ᴴ * K k j) * ρ).trace := by rw [Finset.sum_mul, Matrix.trace_sum]
    _ = 1 := by rw [kraus_complete, Matrix.one_mul, hρ.2]

theorem mixture_density {ι : Type*} [Fintype ι] {n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Matrix ι ι ℂ)
    (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) (hσ : ∀ x, QAlgorithms.IsDensityMatrix (σ x)) :
    QAlgorithms.IsDensityMatrix (∑ x, (p x : ℂ) • σ x) := by
  refine ⟨psd_sum _ _ fun x => (hσ x).1.smul (Complex.zero_le_real.mpr (hp x)), ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, (hσ _).2, smul_eq_mul, mul_one]
  rw [← Complex.ofReal_sum, h1, Complex.ofReal_one]

/-- Pointwise Holevo integrand bound: `χ_k <= Σ_x p_x Tr (N_k ρ_x)^2`. -/
theorem integrand_le (k : Flag 2 2) {n : ℕ} (p : Fin n → ℝ)
    (ρ : Fin n → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) (hρ : ∀ x, QAlgorithms.IsDensityMatrix (ρ x)) :
    QAlgorithms.vnEntropy (∑ x, (p x : ℂ) • retroBranch 2 2 k (ρ x)) -
        ∑ x, p x * QAlgorithms.vnEntropy (retroBranch 2 2 k (ρ x)) ≤
      ∑ x, p x * ((retroBranch 2 2 k (ρ x)) * (retroBranch 2 2 k (ρ x))).trace.re := by
  have hA := entropy_le_one _ (mixture_density p _ hp h1 fun x => retro_density k _ (hρ x))
  have hB : ∑ x, p x * (1 - ((retroBranch 2 2 k (ρ x)) * (retroBranch 2 2 k (ρ x))).trace.re) ≤
      ∑ x, p x * QAlgorithms.vnEntropy (retroBranch 2 2 k (ρ x)) :=
    Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (entropy_ge _ (retro_density k _ (hρ x))) (hp x)
  have hC : ∑ x, p x * (1 - ((retroBranch 2 2 k (ρ x)) * (retroBranch 2 2 k (ρ x))).trace.re) =
      1 - ∑ x, p x * ((retroBranch 2 2 k (ρ x)) * (retroBranch 2 2 k (ρ x))).trace.re := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h1]
  linarith

/-! ### Integration: from the pointwise bound to C_H <= 5/6 -/

theorem scMat : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

attribute [local instance] scMat

theorem scU : SecondCountableTopology (Matrix.unitaryGroup (Fin 2) ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

attribute [local instance] scU

theorem omFlag : OpensMeasurableSpace (Flag 2 2) := by
  unfold Flag
  infer_instance

attribute [local instance] omFlag

lemma haar_isProb (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma flagLaw_isProb : IsProbabilityMeasure (flagLaw 2 2) := by
  have := haar_isProb 2
  unfold flagLaw
  infer_instance

lemma K_cont (j : Fin 2) : Continuous fun k : Flag 2 2 => K k j := by
  refine continuous_pi fun o => continuous_pi fun cd => ?_
  simp only [K, Matrix.of_apply]
  have hv : Continuous (fun M : Matrix.unitaryGroup (Fin 2) ℂ => (M : Matrix (Fin 2) (Fin 2) ℂ)) :=
    continuous_subtype_val
  have hf : Continuous (Prod.fst : Flag 2 2 → Matrix.unitaryGroup (Fin 2) ℂ) := continuous_fst
  have hs : Continuous (fun a : Flag 2 2 => a.2 j) := (continuous_apply j).comp continuous_snd
  have h1 : Continuous fun a : Flag 2 2 => (a.1 : Matrix (Fin 2) (Fin 2) ℂ) cd.1 j :=
    (hv.comp hf).matrix_elem cd.1 j
  have h2 : Continuous fun a : Flag 2 2 => (a.2 j : Matrix (Fin 2) (Fin 2) ℂ) o cd.2 :=
    (hv.comp hs).matrix_elem o cd.2
  exact (continuous_star.comp h1).mul h2

lemma N_cont (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Continuous fun k : Flag 2 2 => retroBranch 2 2 k ρ := by
  have h : (fun k : Flag 2 2 => retroBranch 2 2 k ρ) = fun k => ∑ j, K k j * ρ * (K k j)ᴴ :=
    funext fun k => retro_kraus_form k ρ
  rw [h]
  exact continuous_finsetSum _ fun j _ =>
    ((K_cont j).matrix_mul continuous_const).matrix_mul (K_cont j).matrix_conjTranspose

lemma P_cont (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Continuous fun k : Flag 2 2 => (retroBranch 2 2 k ρ * retroBranch 2 2 k ρ).trace.re :=
  Complex.continuous_re.comp (((N_cont ρ).matrix_mul (N_cont ρ)).matrix_trace)

lemma integrable_of_cont {f : Flag 2 2 → ℝ} (hf : Continuous f) : Integrable f (flagLaw 2 2) := by
  have := flagLaw_isProb
  first
    | exact integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
    | exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- B2 statement: the flag-averaged output purity of `R_{2,2}` is at most `5/6`. -/
def ChildB2 : Prop := ∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, QAlgorithms.IsDensityMatrix ρ →
  ∫ k, (retroBranch 2 2 k ρ * retroBranch 2 2 k ρ).trace.re ∂(flagLaw 2 2) ≤ 5 / 6

theorem holevo_le (hB2 : ChildB2) :
    holevoCapacity (flagLaw 2 2) (retroBranch 2 2) ≤ ENNReal.ofReal (5 / 6) := by
  unfold holevoCapacity
  refine iSup_le fun n => iSup_le fun p => iSup_le fun ρ => iSup_le fun h => ?_
  obtain ⟨hp, h1, hρ⟩ := h
  have := flagLaw_isProb
  unfold flaggedHolevo
  have hint : ∀ x, Integrable
      (fun k => (retroBranch 2 2 k (ρ x) * retroBranch 2 2 k (ρ x)).trace.re) (flagLaw 2 2) :=
    fun x => integrable_of_cont (P_cont _)
  have hnn : ∀ k x, 0 ≤ (retroBranch 2 2 k (ρ x) * retroBranch 2 2 k (ρ x)).trace.re := by
    intro k x
    rw [purity_eig (retro_density k _ (hρ x)).1.1]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsumint : Integrable (fun k => ∑ x, p x *
      (retroBranch 2 2 k (ρ x) * retroBranch 2 2 k (ρ x)).trace.re) (flagLaw 2 2) :=
    integrable_finsetSum _ fun x _ => (hint x).const_mul (p x)
  calc _ ≤ ∫⁻ k, ENNReal.ofReal (∑ x, p x *
          (retroBranch 2 2 k (ρ x) * retroBranch 2 2 k (ρ x)).trace.re) ∂(flagLaw 2 2) :=
        lintegral_mono fun k => ENNReal.ofReal_le_ofReal (integrand_le k p ρ hp h1 hρ)
    _ = ENNReal.ofReal (∫ k, ∑ x, p x *
          (retroBranch 2 2 k (ρ x) * retroBranch 2 2 k (ρ x)).trace.re ∂(flagLaw 2 2)) :=
        (ofReal_integral_eq_lintegral_ofReal hsumint (Filter.Eventually.of_forall fun k =>
          Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (hnn k x))).symm
    _ ≤ ENNReal.ofReal (5 / 6) := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_finsetSum _ fun x _ => (hint x).const_mul (p x)]
      calc ∑ x, ∫ k, p x * (retroBranch 2 2 k (ρ x) * retroBranch 2 2 k (ρ x)).trace.re
            ∂(flagLaw 2 2) ≤ ∑ x, p x * (5 / 6) :=
            Finset.sum_le_sum fun x _ => by
              rw [integral_const_mul]
              exact mul_le_mul_of_nonneg_left (hB2 _ (hρ x)) (hp x)
        _ = 5 / 6 := by rw [← Finset.sum_mul, h1, one_mul]

/-! ### B2 infrastructure: averaging over finitely many measure-preserving left translations -/

theorem bsFlag : BorelSpace (Flag 2 2) := by
  unfold Flag
  infer_instance

attribute [local instance] bsFlag

lemma haar_left (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsMulLeftInvariant := by
  unfold QAlgorithms.Schur.unitaryHaar
  infer_instance

lemma mp_W (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    MeasurePreserving (fun k : Flag 2 2 => (V * k.1, k.2)) (flagLaw 2 2) (flagLaw 2 2) := by
  have := haar_isProb 2
  have := haar_left 2
  unfold flagLaw
  exact (measurePreserving_mul_left (QAlgorithms.Schur.unitaryHaar 2) V).prod (MeasurePreserving.id _)

lemma mp_U1 (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    MeasurePreserving (fun k : Flag 2 2 => (k.1, fun j => if j = 1 then V * k.2 j else k.2 j))
      (flagLaw 2 2) (flagLaw 2 2) := by
  have := haar_isProb 2
  have := haar_left 2
  unfold flagLaw
  refine (MeasurePreserving.id _).prod (measurePreserving_pi
    (fun _ : Fin 2 => QAlgorithms.Schur.unitaryHaar 2) (fun _ : Fin 2 => QAlgorithms.Schur.unitaryHaar 2)
    (f := fun j u => if j = 1 then V * u else u) fun j => ?_)
  by_cases h : j = 1
  · simp only [h, ↓reduceIte]
    exact measurePreserving_mul_left _ V
  · simp only [h, ↓reduceIte]
    exact MeasurePreserving.id _

lemma avg_bound {ι : Type*} [Fintype ι] [Nonempty ι] (T : ι → Flag 2 2 → Flag 2 2)
    (hT : ∀ i, MeasurePreserving (T i) (flagLaw 2 2) (flagLaw 2 2)) (hTc : ∀ i, Continuous (T i))
    (f g : Flag 2 2 → ℝ) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ k, (∑ i, f (T i k)) / Fintype.card ι ≤ g k) :
    ∫ k, f k ∂(flagLaw 2 2) ≤ ∫ k, g k ∂(flagLaw 2 2) := by
  have := flagLaw_isProb
  have e : ∀ i, ∫ k, f (T i k) ∂(flagLaw 2 2) = ∫ k, f k ∂(flagLaw 2 2) := fun i => by
    rw [← integral_map (hTc i).measurable.aemeasurable hf.aestronglyMeasurable, (hT i).map_eq]
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc ∫ k, f k ∂(flagLaw 2 2) = ∫ k, (∑ i, f (T i k)) / Fintype.card ι ∂(flagLaw 2 2) := by
        rw [integral_div, integral_finsetSum _ fun i _ =>
          integrable_of_cont (f := fun k => f (T i k)) (hf.comp (hTc i))]
        simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
    _ ≤ _ := integral_mono
        (integrable_of_cont ((continuous_finsetSum _ fun i _ => hf.comp (hTc i)).div_const _))
        (integrable_of_cont hg) h


/-! ### B2 step 1: twirl U_1 by the real Pauli group -/

noncomputable def Xm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
noncomputable def Ym : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]
noncomputable def Zm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
noncomputable def Cm : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨1/2, -1/2⟩, ⟨-1/2, -1/2⟩; ⟨1/2, -1/2⟩, ⟨1/2, 1/2⟩]

noncomputable def Pm (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := ![1, Xm, Ym, Zm] i
noncomputable def Cpm (m : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := ![1, Cm, Cm * Cm] m

lemma ePm0 : Pm 0 = 1 := rfl
lemma ePm1 : Pm 1 = Xm := rfl
lemma ePm2 : Pm 2 = Ym := rfl
lemma ePm3 : Pm 3 = Zm := rfl
lemma eCpm0 : Cpm 0 = 1 := rfl
lemma eCpm1 : Cpm 1 = Cm := rfl
lemma eCpm2 : Cpm 2 = Cm * Cm := rfl

lemma Pm_mem (i : Fin 4) : Pm i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Pm, Xm, Ym, Zm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

lemma Cm_mem : Cm ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Cm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.ext_iff] <;> norm_num

noncomputable def Pu (i : Fin 4) : Matrix.unitaryGroup (Fin 2) ℂ := ⟨Pm i, Pm_mem i⟩
noncomputable def Cu : Matrix.unitaryGroup (Fin 2) ℂ := ⟨Cm, Cm_mem⟩
noncomputable def Cp (m : Fin 3) : Matrix.unitaryGroup (Fin 2) ℂ := ![1, Cu, Cu * Cu] m

lemma Cp_coe (m : Fin 3) : ((Cp m : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Cpm m := by
  fin_cases m <;> rfl

noncomputable def T1 (i : Fin 4) (k : Flag 2 2) : Flag 2 2 :=
  (k.1, fun j => if j = 1 then Pu i * k.2 j else k.2 j)

noncomputable def T2 (v : Fin 4 × Fin 3) (k : Flag 2 2) : Flag 2 2 :=
  (Pu v.1 * Cp v.2 * k.1, k.2)

lemma T1_cont (i : Fin 4) : Continuous (T1 i) := by
  unfold T1
  refine continuous_fst.prodMk (continuous_pi fun j => ?_)
  by_cases h : j = 1
  · simp only [h, ↓reduceIte]
    exact (continuous_const_mul _).comp ((continuous_apply 1).comp continuous_snd)
  · simp only [h, ↓reduceIte]
    exact (continuous_apply j).comp continuous_snd

lemma T2_cont (v : Fin 4 × Fin 3) : Continuous (T2 v) := by
  unfold T2
  exact ((continuous_const_mul _).comp continuous_fst).prodMk continuous_snd

lemma T2_coe (v : Fin 4 × Fin 3) (k : Flag 2 2) :
    (((T2 v k).1 : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Pm v.1 * (Cpm v.2 * (k.1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  show (Pm v.1 * ((Cp v.2 : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) *
    (k.1 : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [Cp_coe, Matrix.mul_assoc]

lemma K_T1_0 (i : Fin 4) (k : Flag 2 2) : K (T1 i k) 0 = K k 0 := by
  ext o cd
  simp [K, T1]

lemma K_T1_1 (i : Fin 4) (k : Flag 2 2) : K (T1 i k) 1 = Pm i * K k 1 := by
  ext o cd
  simp only [K, T1, ↓reduceIte, Matrix.of_apply]
  rw [show ((Pu i * k.2 1 : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    Pm i * (k.2 1 : Matrix (Fin 2) (Fin 2) ℂ) from rfl]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

noncomputable def Am (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k : Flag 2 2) (j : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ := K k j * ρ * (K k j)ᴴ

noncomputable def q0 (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k : Flag 2 2) : ℝ :=
  (Am ρ k 0).trace.re

noncomputable def g1 (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k : Flag 2 2) : ℝ :=
  1 - q0 ρ k * (1 - q0 ρ k)

lemma g1_cont (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Continuous (g1 ρ) := by
  have hq : Continuous (q0 ρ) := Complex.continuous_re.comp
    ((((K_cont 0).matrix_mul continuous_const).matrix_mul (K_cont 0).matrix_conjTranspose).matrix_trace)
  exact continuous_const.sub (hq.mul (continuous_const.sub hq))

lemma N_T1 (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (i : Fin 4) (k : Flag 2 2) :
    retroBranch 2 2 (T1 i k) ρ = Am ρ k 0 + Pm i * Am ρ k 1 * (Pm i)ᴴ := by
  rw [retro_kraus_form, Fin.sum_univ_two, K_T1_0, K_T1_1, Matrix.conjTranspose_mul]
  simp only [Am, Matrix.mul_assoc]

lemma twirl (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ i : Fin 4, ((A + Pm i * B * (Pm i)ᴴ) * (A + Pm i * B * (Pm i)ᴴ)).trace =
      4 * (A * A).trace + 4 * (B * B).trace + 4 * (A.trace * B.trace) := by
  simp only [Fin.sum_univ_four, ePm0, ePm1, ePm2, ePm3, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
  simp [Xm, Ym, Zm, Matrix.one_apply]
  ring

lemma psd_pur (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    (A * A).trace.re ≤ A.trace.re ^ 2 ∧ A.trace.im = 0 := by
  have hn := hA.eigenvalues_nonneg
  have h2 : ((∑ j, hA.1.eigenvalues j : ℝ) : ℂ) = A.trace := by
    push_cast
    exact hA.1.trace_eq_sum_eigenvalues.symm
  rw [purity_eig hA.1, ← h2, Complex.ofReal_re, Complex.ofReal_im]
  simp only [Fin.sum_univ_two]
  exact ⟨by nlinarith [hn 0, hn 1], by simp⟩

lemma step1_pt (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (k : Flag 2 2) :
    (∑ i : Fin 4, (retroBranch 2 2 (T1 i k) ρ * retroBranch 2 2 (T1 i k) ρ).trace.re) /
      (Fintype.card (Fin 4) : ℝ) ≤ g1 ρ k := by
  have h0 := psd_pur (Am ρ k 0) (hρ.1.mul_mul_conjTranspose_same (K k 0))
  have h1 := psd_pur (Am ρ k 1) (hρ.1.mul_mul_conjTranspose_same (K k 1))
  have ht : (Am ρ k 0).trace + (Am ρ k 1).trace = 1 := by
    have := (retro_density k ρ hρ).2
    rw [retro_kraus_form, Fin.sum_univ_two, Matrix.trace_add] at this
    exact this
  have hre := congrArg Complex.re ht
  simp only [Complex.add_re, Complex.one_re] at hre
  simp only [N_T1]
  rw [← Complex.re_sum, twirl]
  simp only [Fintype.card_fin, g1, q0, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, h0.2, h1.2]
  have e1 : (Am ρ k 1).trace.re = 1 - (Am ρ k 0).trace.re := by linarith
  rw [e1] at h1 ⊢
  nlinarith [h0.1, h1.1]

/-! ### B2 step 2: average W over the 12-element tetrahedral subgroup -/

noncomputable def Qf (r1 r2 r3 : ℝ) (a b : ℂ) : ℝ :=
  r1 * (2 * (star a * b).re) + r2 * (2 * (star a * b).im) + r3 * (Complex.normSq a - Complex.normSq b)

lemma mul00 (M W : Matrix (Fin 2) (Fin 2) ℂ) : (M * W) 0 0 = M 0 0 * W 0 0 + M 0 1 * W 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma mul10 (M W : Matrix (Fin 2) (Fin 2) ℂ) : (M * W) 1 0 = M 1 0 * W 0 0 + M 1 1 * W 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma QX (r1 r2 r3 : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    Qf r1 r2 r3 ((Xm * W) 0 0) ((Xm * W) 1 0) = Qf r1 (-r2) (-r3) (W 0 0) (W 1 0) := by
  rw [mul00, mul10]
  simp [Xm, Qf, Complex.normSq_apply] <;> ring

lemma QY (r1 r2 r3 : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    Qf r1 r2 r3 ((Ym * W) 0 0) ((Ym * W) 1 0) = Qf (-r1) r2 (-r3) (W 0 0) (W 1 0) := by
  rw [mul00, mul10]
  simp [Ym, Qf, Complex.normSq_apply] <;> ring

lemma QZ (r1 r2 r3 : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    Qf r1 r2 r3 ((Zm * W) 0 0) ((Zm * W) 1 0) = Qf (-r1) (-r2) r3 (W 0 0) (W 1 0) := by
  rw [mul00, mul10]
  simp [Zm, Qf, Complex.normSq_apply] <;> ring

lemma QC (r1 r2 r3 : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    Qf r1 r2 r3 ((Cm * W) 0 0) ((Cm * W) 1 0) = Qf r2 r3 r1 (W 0 0) (W 1 0) := by
  rw [mul00, mul10]
  simp [Cm, Qf, Complex.normSq_apply] <;> ring

lemma bloch_sum (r1 r2 r3 : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hN : Complex.normSq (W 0 0) + Complex.normSq (W 1 0) = 1) (hr : r1 ^ 2 + r2 ^ 2 + r3 ^ 2 ≤ 1) :
    ∑ v : Fin 4 × Fin 3, (Qf r1 r2 r3 ((Pm v.1 * (Cpm v.2 * W)) 0 0) ((Pm v.1 * (Cpm v.2 * W)) 1 0)) ^ 2
      ≤ 4 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, ePm0, ePm1, ePm2, ePm3, eCpm0, eCpm1, eCpm2,
    Matrix.one_mul, Matrix.mul_assoc, QX, QY, QZ, QC]
  have hB : (2 * (star (W 0 0) * W 1 0).re) ^ 2 + (2 * (star (W 0 0) * W 1 0).im) ^ 2 +
      (Complex.normSq (W 0 0) - Complex.normSq (W 1 0)) ^ 2 = 1 := by
    have e : (2 * (star (W 0 0) * W 1 0).re) ^ 2 + (2 * (star (W 0 0) * W 1 0).im) ^ 2 +
        (Complex.normSq (W 0 0) - Complex.normSq (W 1 0)) ^ 2 =
        (Complex.normSq (W 0 0) + Complex.normSq (W 1 0)) ^ 2 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.normSq_apply]
      ring
    rw [e, hN]
    norm_num
  simp only [Qf]
  set B1 := 2 * (star (W 0 0) * W 1 0).re
  set B2 := 2 * (star (W 0 0) * W 1 0).im
  set B3 := Complex.normSq (W 0 0) - Complex.normSq (W 1 0)
  calc _ = 4 * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) * (B1 ^ 2 + B2 ^ 2 + B3 ^ 2) := by ring
    _ ≤ 4 := by rw [hB]; nlinarith

noncomputable def sig (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun c c' => ∑ d, ρ (c, d) (c', d)

lemma sig_psd (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : ρ.PosSemidef) :
    (sig ρ).PosSemidef := by
  have : sig ρ = ∑ d : Fin 2, ρ.submatrix (fun c => (c, d)) (fun c => (c, d)) := by
    ext c c'
    simp [sig, Matrix.sum_apply]
  rw [this]
  exact psd_sum _ _ fun d => hρ.submatrix _

lemma sig_facts (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    (sig ρ 0 0).re + (sig ρ 1 1).re = 1 ∧ sig ρ 1 0 = star (sig ρ 0 1) ∧
      (sig ρ 0 1).re ^ 2 + (sig ρ 0 1).im ^ 2 ≤ (sig ρ 0 0).re * (sig ρ 1 1).re := by
  have hP := sig_psd ρ hρ.1
  have h10 : sig ρ 1 0 = star (sig ρ 0 1) := (hP.1.apply 1 0).symm
  have ht : sig ρ 0 0 + sig ρ 1 1 = 1 := by
    rw [← hρ.2]
    simp only [sig, Matrix.of_apply, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h00 : (sig ρ 0 0).im = 0 := by
    have := congrArg Complex.im (hP.1.apply 0 0)
    simp [Complex.star_def] at this
    linarith
  have h11 : (sig ρ 1 1).im = 0 := by
    have := congrArg Complex.im (hP.1.apply 1 1)
    simp [Complex.star_def] at this
    linarith
  have hd := hP.det_nonneg
  rw [Matrix.det_fin_two, h10] at hd
  have hd' := (Complex.le_def.mp hd).1
  simp [Complex.mul_re, Complex.star_def, h00, h11] at hd'
  refine ⟨by simpa using congrArg Complex.re ht, h10, by nlinarith [hd']⟩

lemma KhK (k : Flag 2 2) (j c d c' d' : Fin 2) :
    ((K k j)ᴴ * K k j) (c, d) (c', d') = (k.1 : Matrix (Fin 2) (Fin 2) ℂ) c j *
      star ((k.1 : Matrix (Fin 2) (Fin 2) ℂ) c' j) * (if d = d' then 1 else 0) := by
  rw [← unit_col (k.2 j) d d', Finset.mul_sum]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, Matrix.of_apply, star_mul', star_star]
  exact Finset.sum_congr rfl fun o _ => by ring

lemma q0_eq (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k : Flag 2 2) :
    q0 ρ k = (∑ c, ∑ c', (k.1 : Matrix (Fin 2) (Fin 2) ℂ) c 0 *
      star ((k.1 : Matrix (Fin 2) (Fin 2) ℂ) c' 0) * sig ρ c' c).re := by
  unfold q0 Am
  rw [Matrix.trace_mul_comm (K k 0 * ρ), ← Matrix.mul_assoc]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := (K k 0)ᴴ * K k 0) (N := ρ),
    Fintype.sum_prod_type, KhK, sig, Matrix.of_apply, Fin.sum_univ_two]
  simp
  ring

lemma col_norm (W : Matrix.unitaryGroup (Fin 2) ℂ) :
    Complex.normSq ((W : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
      Complex.normSq ((W : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = 1 := by
  have h := congrArg Complex.re (unit_col W 0 0)
  simp only [Fin.sum_univ_two, Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, if_true, Complex.one_re] at h
  simp only [Complex.normSq_apply]
  linarith

lemma qW_Q (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (W : Matrix.unitaryGroup (Fin 2) ℂ) :
    2 * (∑ c, ∑ c', (W : Matrix (Fin 2) (Fin 2) ℂ) c 0 *
      star ((W : Matrix (Fin 2) (Fin 2) ℂ) c' 0) * sig ρ c' c).re - 1 =
      Qf (2 * (sig ρ 0 1).re) (-2 * (sig ρ 0 1).im) ((sig ρ 0 0).re - (sig ρ 1 1).re)
        ((W : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ((W : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  obtain ⟨hps, h10, -⟩ := sig_facts ρ hρ
  have hN := col_norm W
  simp only [Fin.sum_univ_two, h10]
  simp only [Qf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply] at hN ⊢
  linear_combination ((sig ρ 0 0).re + (sig ρ 1 1).re) * hN + hps

lemma step2_pt (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (k : Flag 2 2) :
    (∑ v : Fin 4 × Fin 3, g1 ρ (T2 v k)) / (Fintype.card (Fin 4 × Fin 3) : ℝ) ≤ 5 / 6 := by
  obtain ⟨hps, -, hdet⟩ := sig_facts ρ hρ
  have key : ∀ v, 2 * q0 ρ (T2 v k) - 1 =
      Qf (2 * (sig ρ 0 1).re) (-2 * (sig ρ 0 1).im) ((sig ρ 0 0).re - (sig ρ 1 1).re)
        ((Pm v.1 * (Cpm v.2 * (k.1 : Matrix (Fin 2) (Fin 2) ℂ))) 0 0)
        ((Pm v.1 * (Cpm v.2 * (k.1 : Matrix (Fin 2) (Fin 2) ℂ))) 1 0) := by
    intro v
    rw [q0_eq, qW_Q ρ hρ, T2_coe]
  have hr : (2 * (sig ρ 0 1).re) ^ 2 + (-2 * (sig ρ 0 1).im) ^ 2 +
      ((sig ρ 0 0).re - (sig ρ 1 1).re) ^ 2 ≤ 1 := by
    nlinarith [hps, hdet]
  have hsum : ∑ v : Fin 4 × Fin 3, (2 * q0 ρ (T2 v k) - 1) ^ 2 ≤ 4 := by
    simp only [key]
    exact bloch_sum _ _ _ _ (col_norm k.1) hr
  have hg : ∑ v : Fin 4 × Fin 3, g1 ρ (T2 v k) =
      ∑ v : Fin 4 × Fin 3, (3 / 4 + (2 * q0 ρ (T2 v k) - 1) ^ 2 / 4) :=
    Finset.sum_congr rfl fun v _ => by simp only [g1]; ring
  have hd : ∑ x : Fin 4 × Fin 3, (2 * q0 ρ (T2 x k) - 1) ^ 2 / 4 =
      (∑ x : Fin 4 × Fin 3, (2 * q0 ρ (T2 x k) - 1) ^ 2) / 4 := (Finset.sum_div _ _ _).symm
  rw [hg, Finset.sum_add_distrib, hd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  rw [div_le_iff₀ (by norm_num)]
  push_cast
  linarith

theorem childB2 : ChildB2 := by
  intro ρ hρ
  have := flagLaw_isProb
  calc ∫ k, (retroBranch 2 2 k ρ * retroBranch 2 2 k ρ).trace.re ∂(flagLaw 2 2)
      ≤ ∫ k, g1 ρ k ∂(flagLaw 2 2) :=
        avg_bound T1 (fun i => mp_U1 (Pu i)) T1_cont _ _ (P_cont ρ) (g1_cont ρ) (step1_pt ρ hρ)
    _ ≤ ∫ _k, (5 / 6 : ℝ) ∂(flagLaw 2 2) :=
        avg_bound T2 (fun v => mp_W (Pu v.1 * Cp v.2)) T2_cont _ _ (g1_cont ρ) continuous_const
          (step2_pt ρ hρ)
    _ = 5 / 6 := by simp

theorem childB : holevoCapacity (flagLaw 2 2) (retroBranch 2 2) ≤ ENNReal.ofReal (5 / 6) :=
  holevo_le childB2

end RetroCorr.Separation.Draft86121560B

open RetroCorr.Separation in
theorem solution :
    holevoCapacity (flagLaw 2 2) (retroBranch 2 2) <
      twoWayQuantumCapacity (flagLaw 2 2) (retroBranch 2 2) := by
  have hQ : (1 : ENNReal) ≤ twoWayQuantumCapacity (flagLaw 2 2) (retroBranch 2 2) := by
    apply le_sSup
    exact ⟨1, zero_le_one, RetroCorr.Separation.Draft86121560A.childA_proof, by simp⟩
  calc holevoCapacity (flagLaw 2 2) (retroBranch 2 2) ≤ ENNReal.ofReal (5 / 6) :=
        RetroCorr.Separation.Draft86121560B.childB
    _ < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
    _ ≤ _ := hQ
