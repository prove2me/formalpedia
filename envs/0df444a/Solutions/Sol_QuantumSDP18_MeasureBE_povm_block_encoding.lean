-- Prove2me | solution 1 for QuantumSDP18.MeasureBE.povm_block_encoding
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:51:33.190631+00:00
-- url     : https://prove2.me/submissions/bce9a0ef-b241-4327-9a7b-37cd0fc32968

import Theorems.Thm_QuantumSDP18_MeasureBE_trace_identity
import Theorems.Thm_QuantumSDP18_MeasureBE_eq_14_iff_specNorm
import Theorems.Thm_QuantumSDP18_MeasureBE_cnot_identity
import Definitions.Def_QuantumSDP18_MeasureBE_Setting
import Mathlib.LinearAlgebra.Matrix.Reindex

open scoped Matrix ComplexConjugate
noncomputable section
private theorem reindex_unitary {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup J ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  calc
    _ = Matrix.reindex e e (A * Aᴴ) := (map_mul (Matrix.reindexRingEquiv ℂ e) A Aᴴ).symm
    _ = 1 := by
      rw [show A * Aᴴ = 1 from Matrix.mem_unitaryGroup_iff.mp hA]
      exact map_one (Matrix.reindexRingEquiv ℂ e)

private theorem cnot_unitary : QAlgorithms.cnot ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [QAlgorithms.cnot, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fintype.sum_bool]

open QuantumSDP18.MeasureBE
private theorem measurement_unitary {I : Type*} [Fintype I] [DecidableEq I] (c : ℕ)
    (U : Matrix (I × Anc c) (I × Anc c) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (I × Anc c) ℂ) :
    Matrix.reindex (reorder c) (reorder c)
      ((Uprime c U)ᴴ * cnotLast (ι := I) c * Uprime c U) ∈
      Matrix.unitaryGroup ((Anc c × Bool) × I) ℂ := by
  have hUp : Uprime c U ∈ Matrix.unitaryGroup ((I × Anc c) × Bool) ℂ :=
    Matrix.kronecker_mem_unitary hU (Matrix.unitaryGroup Bool ℂ).one_mem
  have hCX : cnotLast (ι := I) c ∈ Matrix.unitaryGroup ((I × Anc c) × Bool) ℂ :=
    reindex_unitary (cnotRegs c) _
      (Matrix.kronecker_mem_unitary (Matrix.unitaryGroup (I × QAlgorithms.Qubits c) ℂ).one_mem cnot_unitary)
  exact reindex_unitary (reorder c) _
    ((Matrix.unitaryGroup ((I × Anc c) × Bool) ℂ).mul_mem
      ((Matrix.unitaryGroup ((I × Anc c) × Bool) ℂ).mul_mem (Unitary.star_mem hUp) hCX) hUp)
private theorem ketZeroPrime_corner {I : Type*} [Fintype I] [DecidableEq I] (c : ℕ)
    (A : Matrix ((I × Anc c) × Bool) ((I × Anc c) × Bool) ℂ) :
    (ketZeroPrime (ι := I) c)ᴴ * A * ketZeroPrime (ι := I) c =
      Matrix.of (fun i j => A ((i,ancZero c),false) ((j,ancZero c),false)) := by
  ext i j
  simp [Matrix.mul_apply, ketZeroPrime, Matrix.conjTranspose_apply, Fintype.sum_prod_type]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

set_option autoImplicit false
open QuantumSDP18.MeasureBE


open scoped ComplexOrder

/-- §4.1, p. 25: if a two-outcome POVM `{M, I − M}` is implemented by attaching `a` ancilla
qubits in `|0⟩`, applying a unitary `U` and accepting when the last qubit reads `0`, with bias at
most `ε` (equation (14)), then `U′† (I ⊗ CNOT) U′` with `U′ = U ⊗ I₂` is a
`(1, a + 1, ε)`-block-encoding of `M` (Definition 2, p. 4; ancilla register moved first). -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) (M : Matrix ι ι ℂ) (ε : ℝ)
    (hU : U ∈ Matrix.unitaryGroup (ι × Anc c) ℂ) (hM : M.PosSemidef) (hIM : (1 - M).PosSemidef)
    (hε : 0 ≤ ε)
    (h14 : ∀ ρ : Matrix ι ι ℂ, IsDensity ρ → ‖accProb c U ρ - (M * ρ).trace‖ ≤ ε) :
    QAlgorithms.IsBlockEncoding ((ancZero c, false) : Anc c × Bool)
      (Matrix.reindex (reorder c) (reorder c)
        ((Uprime c U).conjTranspose * cnotLast (ι := ι) c * Uprime c U)) 1 ε M := by
  have hnorm : QAlgorithms.specNorm (blockK c U - M) ≤ ε := by
    apply (eq_14_iff_specNorm c U M ε hM.1 hε).mp
    intro rho hrho
    have ht := (trace_identity c U rho).2
    simpa only [Matrix.sub_mul, Matrix.trace_sub, ← ht] using h14 rho hrho
  let W := (Uprime c U)ᴴ * cnotLast (ι := ι) c * Uprime c U
  have hK : blockK c U = (ketZeroPrime (ι := ι) c)ᴴ * W * ketZeroPrime c := by
    let K := (ketZeroPrime (ι := ι) c)ᴴ
    let Up := Uprime c U
    let C := cnotLast (ι := ι) c
    have h1 := Matrix.mul_assoc K Upᴴ C
    have h2 := congrArg (fun T : Matrix ι ((ι × Anc c) × Bool) ℂ => T * Up) h1
    have h3 := h2.trans (Matrix.mul_assoc K (Upᴴ * C) Up)
    have h4 := congrArg (fun T : Matrix ι ((ι × Anc c) × Bool) ℂ => T * ketZeroPrime c) h3
    exact (cnot_identity c U).trans h4
  have hcorner : (Matrix.of fun i j : ι =>
      (Matrix.reindex (reorder c) (reorder c) W)
        ((ancZero c,false),i) ((ancZero c,false),j)) = blockK c U := by
    calc
      _ = Matrix.of (fun i j => W ((i,ancZero c),false) ((j,ancZero c),false)) := rfl
      _ = (ketZeroPrime (ι := ι) c)ᴴ * W * ketZeroPrime c :=
        (ketZeroPrime_corner (I := ι) c W).symm
      _ = blockK c U := hK.symm
  refine ⟨measurement_unitary c U hU, ?_⟩
  change QAlgorithms.specNorm ((1 : ℂ) • (Matrix.of fun i j : ι =>
      (Matrix.reindex (reorder c) (reorder c) W)
        ((ancZero c,false),i) ((ancZero c,false),j)) - M) ≤ ε
  rw [one_smul, hcorner]
  exact hnorm