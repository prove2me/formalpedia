-- Prove2me | solution 1 for QuantumInfo.recoveryChannel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:59.340197+00:00
-- url     : https://prove2.me/submissions/bd94daf6-8a8b-4d9c-9def-75f30d04ad51

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_recoveryOp_conj
public import Theorems.Thm_QuantumInfo_one_sub_recoveryProj_mul
public import Theorems.Thm_QuantumInfo_Channel_apply_def
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
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) (k l : κ) :
    (recoveryChannel hP hd hF).apply (F k * ρ * (F l)ᴴ)
      = if k = l then ((d k : ℝ) : ℂ) • ρ else 0 := by
  rw [Channel.apply_def]
  show ∑ o : Option κ, recoveryKraus P F d o * (F k * ρ * (F l)ᴴ) * (recoveryKraus P F d o)ᴴ = _
  rw [Fintype.sum_option]
  have hnone : recoveryKraus P F d none * (F k * ρ * (F l)ᴴ) * (recoveryKraus P F d none)ᴴ
      = 0 := by
    show (1 - recoveryProj P F d) * (F k * ρ * (F l)ᴴ) * (1 - recoveryProj P F d)ᴴ = 0
    have h : (1 - recoveryProj P F d) * (F k * ρ * (F l)ᴴ)
        = ((1 - recoveryProj P F d) * F k * P) * (ρ * P * (F l)ᴴ) := by
      conv_lhs => rw [hρ]
      simp only [Matrix.mul_assoc]
    rw [h, one_sub_recoveryProj_mul hP hd hF, zero_mul, zero_mul]
  rw [hnone, zero_add]
  have hsome : ∀ m, recoveryKraus P F d (some m) * (F k * ρ * (F l)ᴴ)
      * (recoveryKraus P F d (some m))ᴴ
      = if m = k ∧ m = l ∧ d m ≠ 0 then ((d m : ℝ) : ℂ) • ρ else 0 :=
    fun m => recoveryOp_conj hP hd hF hρ m k l
  simp only [hsome]
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, Finset.sum_eq_single k]
    · by_cases hk : d k = 0
      · simp [hk]
      · rw [if_pos ⟨rfl, rfl, hk⟩]
    · intro m _ hmk
      simp [hmk]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · rw [if_neg hkl]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg]
    rintro ⟨rfl, rfl, -⟩
    exact hkl rfl
end QuantumInfo
