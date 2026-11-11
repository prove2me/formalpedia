-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P87.single_basis_reduction
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T15:18:03.322884+00:00
-- url     : https://prove2.me/submissions/22dc712a-1ceb-43f4-8329-9014b5722abe

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup

set_option autoImplicit false

noncomputable section



namespace Prove2Me.S12

open scoped Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Multiplication in a common unitary basis cancels the adjacent inverse factors. -/
theorem conjugate_mul (U : Matrix.unitaryGroup I ℂ) (A B : Matrix I I ℂ) :
    ((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ) *
      ((U : Matrix I I ℂ) * B * (U : Matrix I I ℂ)ᴴ) =
    (U : Matrix I I ℂ) * (A * B) * (U : Matrix I I ℂ)ᴴ := by
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := U.property.1
  calc
    _ = (U : Matrix I I ℂ) * A *
        ((U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)) * B * (U : Matrix I I ℂ)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by simp only [hU, Matrix.mul_one, Matrix.mul_assoc]

/-- A product of matrices diagonal in the same basis is diagonal in that basis. -/
theorem diagonal_basis_list_prod (U : Matrix.unitaryGroup I ℂ)
    (L : List (Matrix I I ℂ))
    (hL : ∀ A ∈ L, ∃ d : I → ℂ,
      A = (U : Matrix I I ℂ) * Matrix.diagonal d * (U : Matrix I I ℂ)ᴴ) :
    ∃ d : I → ℂ, L.prod =
      (U : Matrix I I ℂ) * Matrix.diagonal d * (U : Matrix I I ℂ)ᴴ := by
  induction L with
  | nil =>
      refine ⟨fun _ => 1, ?_⟩
      have hU : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ = 1 := U.property.2
      simp only [List.prod_nil, Matrix.diagonal_one, Matrix.mul_one, hU]
  | cons A L ih =>
      obtain ⟨a, ha⟩ := hL A (List.mem_cons_self ..)
      obtain ⟨b, hb⟩ := ih (fun B hB => hL B (List.mem_cons_of_mem A hB))
      refine ⟨fun i => a i * b i, ?_⟩
      rw [List.prod_cons, ha, hb, conjugate_mul, Matrix.diagonal_mul_diagonal]

/-- The same normal form respects the reversed product used for sequential measurements. -/
theorem diagonal_basis_ordered_product (U : Matrix.unitaryGroup I ℂ)
    {t : ℕ} (f : Fin t → I → ℂ) :
    ∃ d : I → ℂ,
      (List.ofFn (fun j => (U : Matrix I I ℂ) * Matrix.diagonal (f j) *
        (U : Matrix I I ℂ)ᴴ)).reverse.prod =
      (U : Matrix I I ℂ) * Matrix.diagonal d * (U : Matrix I I ℂ)ᴴ := by
  apply diagonal_basis_list_prod U
  intro A hA
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hA)
  exact ⟨f j, hj.symm⟩

/-- Undoing conjugation works for every matrix, without a positivity hypothesis. -/
theorem undo_conjugation (U : Matrix.unitaryGroup I ℂ) (A : Matrix I I ℂ) :
    (U : Matrix I I ℂ)ᴴ *
      ((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ) * (U : Matrix I I ℂ) = A := by
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := U.property.1
  calc
    _ = ((U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)) * A *
        ((U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hU]; simp only [Matrix.one_mul, Matrix.mul_one]

/-- Cyclicity of trace removes a unitary conjugation. -/
theorem trace_conjugation (U : Matrix.unitaryGroup I ℂ) (A : Matrix I I ℂ) :
    ((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ).trace = A.trace := by
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := U.property.1
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- A measurement sandwich may be evaluated after changing into its unitary basis. -/
theorem trace_conjugated_sandwich (U : Matrix.unitaryGroup I ℂ)
    (A R : Matrix I I ℂ) :
    (((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ) * R *
      ((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ)ᴴ).trace =
    (A * ((U : Matrix I I ℂ)ᴴ * R * (U : Matrix I I ℂ)) * Aᴴ).trace := by
  calc
    _ = ((U : Matrix I I ℂ) *
      (A * ((U : Matrix I I ℂ)ᴴ * R * (U : Matrix I I ℂ)) * Aᴴ) *
        (U : Matrix I I ℂ)ᴴ).trace := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    _ = _ := trace_conjugation U _

end Prove2Me.S12



namespace Prove2Me.S12

open scoped Matrix

/-- Diagonal left and right factors only see the middle matrix's diagonal in a trace. -/
theorem trace_diagonal_middle {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ℂ) (R : Matrix I I ℂ) :
    (Matrix.diagonal a * R * Matrix.diagonal b).trace =
      (Matrix.diagonal a * Matrix.diagonal (fun i => R i i) * Matrix.diagonal b).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

/-- In particular, pinching the middle matrix preserves every diagonal sandwich trace. -/
theorem trace_diagonal_sandwich {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → ℂ) (R : Matrix I I ℂ) :
    (Matrix.diagonal d * R * (Matrix.diagonal d)ᴴ).trace =
      (Matrix.diagonal d * Matrix.diagonal (fun i => R i i) *
        (Matrix.diagonal d)ᴴ).trace := by
  rw [Matrix.diagonal_conjTranspose]
  exact trace_diagonal_middle d (star d) R

end Prove2Me.S12

open Prove2Me.S12
open scoped Matrix ComplexConjugate ComplexOrder

/-- The exact published proposition with its reducible definitions expanded. -/
theorem solution {I O : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq O] (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ)
    (hrho : rho.PosSemidef ∧ rho.trace = 1) (t : ℕ)
    (f : Fin t → I → O) (o : Fin t → O) :
    let K := (List.ofFn (fun j : Fin t =>
      (U : Matrix I I ℂ) * Matrix.diagonal (fun i => if f j i = o j then 1 else 0) *
        (U : Matrix I I ℂ)ᴴ)).reverse.prod
    (K * ((U : Matrix I I ℂ) *
      Matrix.diagonal (fun i => ((U : Matrix I I ℂ)ᴴ * rho * (U : Matrix I I ℂ)) i i) *
        (U : Matrix I I ℂ)ᴴ) * Kᴴ).trace.re = (K * rho * Kᴴ).trace.re := by
  obtain ⟨d, hd⟩ := diagonal_basis_ordered_product U
    (fun j i => if f j i = o j then 1 else 0)
  dsimp only
  rw [hd]
  apply congrArg Complex.re
  rw [trace_conjugated_sandwich, trace_conjugated_sandwich, undo_conjugation]
  exact (trace_diagonal_sandwich d ((U : Matrix I I ℂ)ᴴ * rho * (U : Matrix I I ℂ))).symm

#print axioms solution
