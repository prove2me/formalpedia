-- Prove2me | solution 1 for QuantumSDP18.DensityBE.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:04:26.393142+00:00
-- url     : https://prove2.me/submissions/a21db141-8e54-4467-b6ab-f36b5d3577f6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

set_option autoImplicit false
open scoped Kronecker ComplexOrder
open QuantumSDP18.DensityBE


lemma perm_unitary {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) :
    (Matrix.of fun x y => if x = e y then (1 : ℂ) else 0) ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (e.symm a)]
  · by_cases h : a = b <;> simp [h, eq_comm]
  · intro y _ hy
    have : a ≠ e y := fun h => hy (by rw [h]; simp)
    simp [this]
  · simp

theorem V_mem_aux {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Reg w c) ℂ) :
    V G ∈ Matrix.unitaryGroup (Big w c) ℂ := by
  have h1 : ((1 : Matrix (QAlgorithms.Qubits w × Bool) (QAlgorithms.Qubits w × Bool) ℂ) ⊗ₖ G)
      ∈ Matrix.unitaryGroup (Big w c) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff] at hG ⊢
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, mul_one, ← Matrix.star_eq_conjTranspose, hG,
      Matrix.one_kronecker_one]
  have h2 : ((1 : Matrix (QAlgorithms.Qubits w × Bool) (QAlgorithms.Qubits w × Bool) ℂ) ⊗ₖ
      G.conjTranspose) = star ((1 : Matrix (QAlgorithms.Qubits w × Bool)
        (QAlgorithms.Qubits w × Bool) ℂ) ⊗ₖ G) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have h3 : swapReg w c ∈ Matrix.unitaryGroup (Big w c) ℂ := perm_unitary (swapEquiv w c)
  unfold V
  rw [h2]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem h1) h3) h1


lemma gen_entry {X R : Type*} [Fintype X] [Fintype R] [DecidableEq X] [DecidableEq R]
    (G : Matrix R R ℂ) (S : Matrix (X × R) (X × R) ℂ) (z : R) (a b : X) :
    (((1 : Matrix X X ℂ) ⊗ₖ G.conjTranspose) * S * ((1 : Matrix X X ℂ) ⊗ₖ G)) (a, z) (b, z) =
      ∑ r, ∑ r', star (G r z) * S (a, r) (b, r') * G r' z := by
  simp only [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul,
    mul_ite, mul_zero]
  rw [Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp only [if_true]
  have h : ∀ x : R, (∑ x_1 : X, ∑ x_2 : R, if a = x_1 then star (G x_2 z) * S (x_1, x_2) (b, x) * G x z else 0)
      = ∑ x_2 : R, star (G x_2 z) * S (a, x_2) (b, x) * G x z := by
    intro x
    rw [Finset.sum_comm]
    simp
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_comm]

theorem block_aux {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ) :
    (Matrix.of fun i j : QAlgorithms.Qubits w =>
      V G ((i, false), zeroReg w c) ((j, false), zeroReg w c)) =
    sandwich (purifVec G) := by
  ext i j
  simp only [Matrix.of_apply, V, sandwich, purifVec]
  exact gen_entry G (swapReg w c) (zeroReg w c) (i, false) (j, false)


lemma sandwich_apply {w c : ℕ} (φ : Reg w c → ℂ) (i j : QAlgorithms.Qubits w) :
    sandwich φ i j = ∑ t : QAlgorithms.Qubits c, star (φ (j, false, t)) * φ (i, false, t) := by
  simp only [sandwich, Matrix.of_apply, swapReg, swapEquiv, Equiv.coe_fn_mk]
  rw [Finset.sum_comm]
  simp only [Prod.mk.injEq, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [ite_and]
  have h : ∀ x : Reg w c, (∑ y : Reg w c, if i = x.1 then if false = x.2.1 then
      (if y = (j, false, x.2.2) then star (φ y) * φ x else 0) else 0 else 0) =
      if i = x.1 ∧ false = x.2.1 then star (φ (j, false, x.2.2)) * φ x else 0 := by
    intro x
    by_cases h1 : i = x.1 <;> by_cases h2 : false = x.2.1 <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp

theorem flag0eq_aux {w c : ℕ} (φ : Reg w c → ℂ)
    (ϱ : Matrix (QAlgorithms.Qubits w) (QAlgorithms.Qubits w) ℂ)
    (hpur : IsPurification φ ϱ) :
    sandwich (flag0 φ) = ϱ := by
  ext i j
  rw [sandwich_apply]
  have h := congrFun (congrFun hpur.2 i) j
  rw [h]
  simp only [Matrix.of_apply, flag0]
  exact Finset.sum_congr rfl (fun t _ => by simp [mul_comm])


theorem sandwich_flag0_aux {w c : ℕ} (φ : Reg w c → ℂ) :
    sandwich φ = sandwich (flag0 φ) := by
  ext i j
  rw [sandwich_apply, sandwich_apply]
  simp [flag0]

theorem solution {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ)
    (ϱ : Matrix (QAlgorithms.Qubits w) (QAlgorithms.Qubits w) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Reg w c) ℂ)
    (hϱ : IsSubnormDensity ϱ)
    (hpur : IsPurification (purifVec G) ϱ) :
    QAlgorithms.IsBlockEncoding (ancZero w c)
      (Matrix.reindex (blockEquiv w c) (blockEquiv w c) (V G)) 1 0 ϱ := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    have hV := Matrix.mem_unitaryGroup_iff.mp (V_mem_aux G hG)
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex, ← Matrix.star_eq_conjTranspose,
      ← Matrix.reindexAlgEquiv_apply ℂ ℂ (blockEquiv w c), ← Matrix.reindexAlgEquiv_apply ℂ ℂ (blockEquiv w c),
      ← map_mul, hV]
    exact (Matrix.reindexAlgEquiv ℂ ℂ (blockEquiv w c)).map_one
  · have hb : (Matrix.of fun i j : QAlgorithms.Qubits w =>
        Matrix.reindex (blockEquiv w c) (blockEquiv w c) (V G) (ancZero w c, i) (ancZero w c, j)) = ϱ := by
      have h1 := block_aux G
      have h2 := flag0eq_aux (purifVec G) ϱ hpur
      have h3 : sandwich (purifVec G) = sandwich (flag0 (purifVec G)) := sandwich_flag0_aux (purifVec G)
      rw [← h2, ← h3, ← h1]
      ext i j
      rfl
    rw [hb]
    have h0 : ((1 : ℝ) : ℂ) • ϱ - ϱ = 0 := by simp
    rw [h0, QAlgorithms.specNorm]
    let : NormedAddCommGroup (Matrix (QAlgorithms.Qubits w) (QAlgorithms.Qubits w) ℂ) :=
      Matrix.instL2OpNormedAddCommGroup
    exact le_of_eq norm_zero
