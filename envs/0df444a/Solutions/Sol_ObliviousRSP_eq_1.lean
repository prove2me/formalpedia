-- Prove2me | solution 1 for ObliviousRSP.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:34:29.807884+00:00
-- url     : https://prove2.me/submissions/944347a6-bad7-4f6f-894c-a2d8c1412d18

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState
import Definitions.Def_ObliviousRSP_IsObliviousRSP

open scoped Kronecker Matrix

open ObliviousRSP in
theorem solution {ι σ M : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {K : M → Type} [∀ m, Fintype (K m)] [∀ m, DecidableEq (K m)]
    {S : Set (ι → ℂ)} {E : (ι → ℂ) → M → Matrix σ σ ℂ} {V : (m : M) → Matrix (ι × K m) σ ℂ}
    {p : M → ℝ} {b : (m : M) → Matrix (K m) (K m) ℂ}
    (h : IsObliviousRSP S E V p b) {ψ : ι → ℂ} (hψ : ψ ∈ S) (m : M) :
    bobState (E ψ m) = (p m : ℂ) • ((V m)ᴴ * (pureState ψ ⊗ₖ b m) * V m) := by
  have hf := h.faithful_oblivious ψ hψ m
  have hi := h.isometry m
  have e : (V m)ᴴ * (V m * bobState (E ψ m) * (V m)ᴴ) * V m = bobState (E ψ m) := by
    simp only [← Matrix.mul_assoc]
    rw [hi, Matrix.one_mul, Matrix.mul_assoc, hi, Matrix.mul_one]
  rw [← e, hf, Matrix.mul_smul, Matrix.smul_mul]
