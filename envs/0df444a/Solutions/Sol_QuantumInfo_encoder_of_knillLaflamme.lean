-- Prove2me | solution 1 for QuantumInfo.encoder_of_knillLaflamme
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:37.887157+00:00
-- url     : https://prove2.me/submissions/ee8a932a-c417-48e7-b86f-5240b4524b36

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
variable {L : Type*} [Fintype L] [DecidableEq L] {V : Matrix n L ℂ}
omit [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype L]
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P) (hV : Vᴴ * V = 1) (hPV : P * V = V)
    (hc : KnillLaflamme P E c) (i j : ι) : Vᴴ * (E i)ᴴ * E j * V = c i j • 1 := by
  have hVP : Vᴴ * P = Vᴴ := by
    conv_lhs => rw [← hP.conjTranspose_eq]
    rw [← conjTranspose_mul, hPV]
  calc Vᴴ * (E i)ᴴ * E j * V
      = Vᴴ * P * (E i)ᴴ * E j * (P * V) := by rw [hVP, hPV]
    _ = Vᴴ * (P * (E i)ᴴ * E j * P) * V := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * (c i j • P) * V := by rw [hc i j]
    _ = c i j • (Vᴴ * P * V) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = c i j • 1 := by rw [hVP, hV]
end QuantumInfo
