-- Prove2me | solution 1 for ObliviousRSP.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:49:36.980493+00:00
-- url     : https://prove2.me/submissions/2c7aaa32-d935-4e06-afe0-444fbd2201f3

import Mathlib
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState

open scoped Kronecker

open ObliviousRSP in
theorem solution {σ M : Type} [Fintype σ] [DecidableEq σ] (E' : M → Matrix σ σ ℂ)
    (hE : IsPOVM E') :
    HasSum (fun m => bobState (E' m)) ((Fintype.card σ : ℂ)⁻¹ • (1 : Matrix σ σ ℂ)) := by
  let L : Matrix σ σ ℂ →ₗ[ℂ] Matrix σ σ ℂ :=
    { toFun := bobState
      map_add' := by
        intro A B
        unfold bobState WildeQIT.partialTraceLeft
        ext k l
        simp only [Matrix.add_kronecker, Matrix.add_mul, Matrix.of_apply, Matrix.add_apply,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c A
        unfold bobState WildeQIT.partialTraceLeft
        ext k l
        simp only [Matrix.smul_kronecker, Matrix.smul_mul, Matrix.of_apply, Matrix.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  have h := hE.2.map L hcont
  have h1 : L 1 = (Fintype.card σ : ℂ)⁻¹ • (1 : Matrix σ σ ℂ) := by
    change bobState 1 = _
    unfold bobState WildeQIT.partialTraceLeft maxEnt
    ext k l
    rw [Matrix.one_kronecker_one, Matrix.one_mul]
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hkl : k = l
    · subst hkl
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ k) h
    · rw [if_neg hkl, mul_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hkl (h1.symm.trans h2)
  rw [h1] at h
  exact h
