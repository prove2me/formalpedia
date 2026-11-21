-- Prove2me | solution 1 for QuantumInfo.recoveryOp_mul_mul_codeProj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:28.865653+00:00
-- url     : https://prove2.me/submissions/d9e97895-0133-4001-a1f4-bad5b59e821c

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_Channel_id_apply
attribute [local simp] QuantumInfo.Channel.id_apply



set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}
omit [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [DecidableEq κ]
variable (P : Matrix n n ℂ) (F : κ → Matrix n n ℂ) (d : κ → ℝ)
variable [Fintype κ]
variable {P F d}
omit [DecidableEq n] [Fintype κ]
namespace QuantumInfo
theorem _root_.solution
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) (m k : κ) :
    recoveryOp P F d m * F k * P
      = if m = k ∧ d m ≠ 0 then ((Real.sqrt (d m) : ℝ) : ℂ) • P else 0 := by
  unfold recoveryOp
  by_cases hm : d m = 0
  · simp [hm]
  rw [if_neg hm, Matrix.smul_mul, Matrix.smul_mul, hF m k]
  by_cases hmk : m = k
  · subst hmk
    rw [if_pos rfl, if_pos ⟨rfl, hm⟩, smul_smul, ← Complex.ofReal_mul, inv_mul_eq_div,
      Real.div_sqrt]
  · simp [hmk]
end QuantumInfo
