-- Prove2me | solution 1 for WildeQIT.Purification.purifications_related_by_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:42:39.049167+00:00
-- url     : https://prove2.me/submissions/61b3dfe7-5005-4d0d-82bc-0a35974dbcd9

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics
import Definitions.Def_WildeQIT_Purification_IsPurification
import Theorems.Thm_WildeQIT_Purification_exists_coisometry_eq_mul_of_mul_conjTranspose_eq

open Matrix WildeQIT.Purification
open scoped Kronecker

theorem solution {a R1 R2 : Type} [Fintype a] [DecidableEq a]
    [Fintype R1] [DecidableEq R1] [Fintype R2]
    (ρ : Matrix a a ℂ) (ψ : R1 × a → ℂ) (φ : R2 × a → ℂ)
    (hψ : IsPurification ρ ψ) (hφ : IsPurification ρ φ)
    (hdim : Fintype.card R1 ≤ Fintype.card R2) :
    ∃ U : Matrix R2 R1 ℂ, HarlowTASI.IsIsometry U ∧ φ = (U ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ ψ := by
  classical
  let Ψ : Matrix a R1 ℂ := Matrix.of fun x r => ψ (r, x)
  let Φ : Matrix a R2 ℂ := Matrix.of fun x r => φ (r, x)
  have hΨ : Ψ * Ψᴴ = ρ := by
    rw [← hψ.2]
    ext x y
    simp [Ψ, Matrix.mul_apply, WildeQIT.partialTraceLeft, vecMulVec_apply]
  have hΦ : Φ * Φᴴ = ρ := by
    rw [← hφ.2]
    ext x y
    simp [Φ, Matrix.mul_apply, WildeQIT.partialTraceLeft, vecMulVec_apply]
  obtain ⟨V, hV, hΦΨ⟩ := exists_coisometry_eq_mul_of_mul_conjTranspose_eq Φ Ψ hdim (hΦ.trans hΨ.symm)
  refine ⟨Matrix.of fun r2 r1 => V r1 r2, ?_, ?_⟩
  · unfold HarlowTASI.IsIsometry
    ext r r'
    have := congrFun (congrFun hV r') r
    simp only [Matrix.mul_apply, conjTranspose_apply, of_apply, Matrix.one_apply] at this ⊢
    rw [show (if r = r' then (1 : ℂ) else 0) = if r' = r then 1 else 0 by
      by_cases hrr : r = r'
      · simp [hrr]
      · simp [hrr, Ne.symm hrr], ← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  · funext ⟨r2, x⟩
    have := congrFun (congrFun hΦΨ x) r2
    simp only [Φ, Ψ, of_apply, Matrix.mul_apply] at this
    rw [this]
    simp only [Matrix.mulVec, dotProduct, kroneckerMap_apply, Matrix.one_apply, of_apply,
      Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun r1 _ => ?_
    ring
