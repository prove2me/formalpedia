-- Prove2me | solution 1 for TranscendenceTheory.integer_grid_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T10:15:49.808339+00:00
-- url     : https://prove2.me/submissions/b45c0253-c721-434b-8d4e-fe7bad909238

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open WeierstrassEllipticZeta

theorem solution
    (Λ : Submodule ℤ ℂ) (ω u₁ u₂ : ℂ)
    (hω : ω ∈ Λ)
    (h_independent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ Λ = ⊥) :
    Function.Injective (integerGridPoint u₁ u₂ ω) ∧
    (∀ m : Fin 3 → ℤ,
      integerGridPoint u₁ u₂ ω m ∈ Λ ↔ m 0 = 0 ∧ m 1 = 0) ∧
    (∀ m : Fin 3 → ℤ, integerGridPoint u₁ u₂ ω m + u₁ / 2 ∉ Λ) ∧
    (∀ m n : Fin 3 → ℤ,
      integerGridPoint u₁ u₂ ω m - integerGridPoint u₁ u₂ ω n ∈ Λ ↔
        m 0 = n 0 ∧ m 1 = n 1) := by
  have hi : LinearIndependent ℤ ![u₁, u₂, ω] :=
    h_independent.restrict_scalars' ℤ
  have hinj : Function.Injective (integerGridPoint u₁ u₂ ω) := by
    intro m n h
    apply hi.fintypeLinearCombination_injective
    simpa [Fintype.linearCombination_apply, Fin.sum_univ_succ,
      integerGridPoint, zsmul_eq_mul, add_assoc] using h
  have hzero (a b : ℤ) (h : (a : ℂ) * u₁ + (b : ℂ) * u₂ = 0) :
      a = 0 ∧ b = 0 := by
    have hm : (![a, b, 0] : Fin 3 → ℤ) = 0 := hinj (by
      simpa [integerGridPoint] using h)
    exact ⟨by simpa using congrFun hm 0, by simpa using congrFun hm 1⟩
  have hlat (m : Fin 3 → ℤ) :
      integerGridPoint u₁ u₂ ω m ∈ Λ ↔ m 0 = 0 ∧ m 1 = 0 := by
    constructor
    · intro hm
      have hsub : (m 0 : ℂ) * u₁ + (m 1 : ℂ) * u₂ ∈ Λ := by
        simpa [integerGridPoint, zsmul_eq_mul] using
          Λ.sub_mem hm (Λ.smul_mem (m 2) hω)
      have hspan : (m 0 : ℂ) * u₁ + (m 1 : ℂ) * u₂ ∈
          Submodule.span ℤ {u₁, u₂} := by
        simpa [zsmul_eq_mul] using
          (Submodule.span ℤ {u₁, u₂}).add_mem
            ((Submodule.span ℤ {u₁, u₂}).smul_mem (m 0)
              (Submodule.subset_span (by simp)))
            ((Submodule.span ℤ {u₁, u₂}).smul_mem (m 1)
              (Submodule.subset_span (by simp)))
      have hz : (m 0 : ℂ) * u₁ + (m 1 : ℂ) * u₂ = 0 := by
        have hm' : (m 0 : ℂ) * u₁ + (m 1 : ℂ) * u₂ ∈
            Submodule.span ℤ {u₁, u₂} ⊓ Λ := ⟨hspan, hsub⟩
        simpa [h_intersection] using hm'
      exact hzero _ _ hz
    · rintro ⟨ha, hb⟩
      simpa [integerGridPoint, ha, hb, zsmul_eq_mul] using Λ.smul_mem (m 2) hω
  refine ⟨hinj, hlat, ?_, ?_⟩
  · intro m hm
    have hd : integerGridPoint u₁ u₂ ω
        ![2 * m 0 + 1, 2 * m 1, 2 * m 2] ∈ Λ := by
      convert Λ.smul_mem (2 : ℤ) hm using 1
      simp [integerGridPoint, zsmul_eq_mul]
      ring
    have hodd := ((hlat _).mp hd).1
    change 2 * m 0 + 1 = 0 at hodd
    omega
  · intro m n
    have heq : integerGridPoint u₁ u₂ ω m - integerGridPoint u₁ u₂ ω n =
        integerGridPoint u₁ u₂ ω (m - n) := by
      simp [integerGridPoint, sub_mul]
      ring
    rw [heq, hlat]
    simp [sub_eq_zero]

