-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.invariantDissipator_singleField
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:58:12.036727+00:00
-- url     : https://prove2.me/submissions/67344b95-1da8-4184-bd80-1deacbbba610

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

/-- the dissipator for a jump family -/
def X7ID_dis {n r : ℕ} (W : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  cpGenerator ((1 / 2 : ℂ) • ∑ k, (W k)ᴴ * W k) W

lemma X7ID_dis_apply {n r : ℕ} (W : Fin r → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    X7ID_dis W X = (∑ k, W k * X * (W k)ᴴ) - ((1 / 2 : ℂ) • ∑ k, (W k)ᴴ * W k) * X -
      X * ((1 / 2 : ℂ) • ∑ k, (W k)ᴴ * W k)ᴴ := by
  simp [X7ID_dis, cpGenerator, sandwich, LinearMap.sum_apply, Matrix.mul_assoc]

lemma X7ID_e1 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (A * (Matrix.single j j 1 : Matrix (Fin n) (Fin n) ℂ) * B) i i = A i j * B j i := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

lemma X7ID_e2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (A * (Matrix.single j j 1 : Matrix (Fin n) (Fin n) ℂ)) i i = if i = j then A j j else 0 := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  split_ifs <;> simp_all

lemma X7ID_e3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ((Matrix.single j j 1 : Matrix (Fin n) (Fin n) ℂ) * A) i i = if i = j then A j j else 0 := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  split_ifs <;> simp_all

lemma X7ID_rates1 {n r : ℕ} (W : Fin r → Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    rates W 1 i j = ∑ k, Complex.normSq (W k i j) := by
  simp [rates]

lemma X7ID_pg {n r : ℕ} (W : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    populationGenerator W U i j = rates W U i j - if i = j then ∑ l, rates W U l j else 0 := by
  simp [populationGenerator, Matrix.diagonal_apply]
  split_ifs <;> simp_all

lemma X7ID_popGen_entry {n r : ℕ} (W : Fin r → Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ((populationGenerator W 1 i j : ℝ) : ℂ) =
      X7ID_dis W (Matrix.single j j 1) i i := by
  rw [X7ID_dis_apply]
  rw [Matrix.sub_apply, Matrix.sub_apply, X7ID_e2, X7ID_e3, Matrix.sum_apply]
  simp only [X7ID_e1, Matrix.conjTranspose_apply]
  have hK : (((1 / 2 : ℂ) • ∑ k, (W k)ᴴ * W k) j j) =
      (((1 / 2 : ℝ) * ∑ k, ∑ l, Complex.normSq (W k l j) : ℝ) : ℂ) := by
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      smul_eq_mul]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]; exact Complex.mul_conj _
  rw [hK, Complex.star_def, Complex.conj_ofReal]
  rw [X7ID_pg]
  simp only [X7ID_rates1]
  simp only [Complex.mul_conj]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    push_cast
    rw [Finset.sum_comm (f := fun x y => (Complex.normSq (W y x i) : ℂ))]
    ring
  · simp [hij]


lemma X7ID_conj {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U X : Matrix (Fin n) (Fin n) ℂ)
    (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1) :
    Uᴴ * X7ID_dis V (U * X * Uᴴ) * U = X7ID_dis (fun k => Uᴴ * V k * U) X := by
  have e1 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e2 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [X7ID_dis_apply, X7ID_dis_apply]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum, Finset.sum_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum, Matrix.mul_smul, Matrix.smul_mul, e1, e2, h1, Matrix.mul_one]

lemma X7ID_pg_conj {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    populationGenerator V U = populationGenerator (fun k => Uᴴ * V k * U) 1 := by
  ext i j
  simp [X7ID_pg, rates]

lemma X7ID_const {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ X,
      X7ID_dis V (U * X * Uᴴ) = U * X7ID_dis V X * Uᴴ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    populationGenerator V U = populationGenerator V 1 := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  rw [X7ID_pg_conj]
  ext i j
  apply Complex.ofReal_injective
  rw [X7ID_popGen_entry, X7ID_popGen_entry, ← X7ID_conj V U _ h1 h2, h]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  exact hU


lemma X7ID_perm_unitary {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change σ.permMatrix ℂ * (σ.permMatrix ℂ)ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

lemma X7ID_pg_perm {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    populationGenerator V (σ.permMatrix ℂ) i j = populationGenerator V 1 (σ.symm i) (σ.symm j) := by
  have hr : ∀ a b, rates V (σ.permMatrix ℂ) a b = rates V 1 (σ.symm a) (σ.symm b) := by
    intro a b
    simp only [rates, Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one, Matrix.submatrix_apply, id]
    rfl
  rw [X7ID_pg, X7ID_pg, hr]
  simp only [hr, σ.symm.injective.eq_iff]
  split_ifs
  · rw [Equiv.sum_comp σ.symm (fun l => rates V 1 l (σ.symm j))]
  · rfl

end QAlgorithms.Papers.Independent.Dependency50.P16

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Dependency50.P16 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (h : invariantDissipator D) :
    (∃ A : RMat n, fields D = {A} ∧ ∀ p : Equiv.Perm (Fin n),
      ∀ x : (fun n : ℕ => Fin n → ℝ) n, A *ᵥ (fun i => x (p i)) = fun i => (A *ᵥ x) (p i)) ∧
    (2 < n → nowhereDirectlyAccessible D) := by
  have hc : ∀ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ →
      populationGenerator D.jump U = populationGenerator D.jump 1 :=
    X7ID_const D.jump (fun U hU X => h U hU X)
  have hf : fields D = {populationGenerator D.jump 1} := by
    ext B
    simp only [fields, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact hc U hU.1
    · rintro rfl
      exact ⟨1, ⟨one_mem _, Matrix.det_one⟩, rfl⟩
  have hsym : ∀ (p : Equiv.Perm (Fin n)) (i j : Fin n),
      populationGenerator D.jump 1 (p i) (p j) = populationGenerator D.jump 1 i j := by
    intro p i j
    have := X7ID_pg_perm D.jump p (p i) (p j)
    rw [hc _ (X7ID_perm_unitary _)] at this
    simpa using this
  refine ⟨⟨populationGenerator D.jump 1, hf, ?_⟩, ?_⟩
  · intro p x
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp p (fun j => populationGenerator D.jump 1 (p i) j * x j)]
    simp only [hsym]
  · intro h2 x _ hacc
    set v := populationGenerator D.jump 1 *ᵥ x with hv
    have hder : derivatives D x = {v} := by
      ext w
      simp only [derivatives, hf, Set.mem_singleton_iff, Set.mem_ofPred_eq, exists_eq_left]
      exact Iff.rfl
    unfold directlyAccessible at hacc
    rw [hder] at hacc
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    let i2 : Fin n := ⟨2, by omega⟩
    have hmem : ∀ a b : Fin n, (Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) ∈ zeroSum n := by
      intro a b
      simp [zeroSum, Finset.sum_sub_distrib]
    have hu := hmem i0 i1
    have hw := hmem i0 i2
    rw [← hacc, Submodule.mem_span_singleton] at hu hw
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hw
    have ha2 := congrFun ha i2
    have hb2 := congrFun hb i2
    have ha0 := congrFun ha i0
    have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    simp [Pi.single_apply, h02.symm, h12.symm, h01.symm] at ha2 hb2 ha0
    rcases ha2 with ha2 | ha2
    · subst ha2; simp at ha0
    · rw [ha2] at hb2; simp at hb2
