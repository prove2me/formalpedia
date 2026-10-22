-- Prove2me | solution 1 for ProcureAssort.Hotelling.lemma_F_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T03:13:21.301478+00:00
-- url     : https://prove2.me/submissions/6c3f5e5b-7e84-4588-a1b3-76d4124c80de

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

open ProcureAssort.Hotelling

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) (m : ι → ℝ) :
    (∃ p : κ → ℝ, Matrix.mulVec M p = m) ↔
      ∀ y : ι → ℝ, Matrix.vecMul y M = 0 → dotProduct y m = 0 := by
  classical
  constructor
  · rintro ⟨p, rfl⟩ y hy
    rw [Matrix.dotProduct_mulVec, hy, zero_dotProduct]
  · intro h
    by_contra hne
    have hm : m ∉ LinearMap.range M.mulVecLin := by
      rintro ⟨p, hp⟩
      exact hne ⟨p, hp⟩
    obtain ⟨φ, hφm, hle⟩ := Submodule.exists_le_ker_of_notMem hm
    set y : ι → ℝ := fun i => φ (Pi.single i 1) with hy
    have hφ : ∀ v : ι → ℝ, φ v = dotProduct y v := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ φ v]
      simp only [dotProduct, smul_eq_mul, hy]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hyM : Matrix.vecMul y M = 0 := by
      have key : ∀ p : κ → ℝ, dotProduct (Matrix.vecMul y M) p = 0 := by
        intro p
        rw [← Matrix.dotProduct_mulVec, ← hφ]
        have : Matrix.mulVec M p ∈ LinearMap.range M.mulVecLin := ⟨p, rfl⟩
        exact hle this
      funext k
      have := key (Pi.single k 1)
      simpa [dotProduct_single] using this
    exact hφm (by rw [hφ]; exact h y hyM)
