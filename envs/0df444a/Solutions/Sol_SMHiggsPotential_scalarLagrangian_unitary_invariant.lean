-- Prove2me | solution 1 for SMHiggsPotential.scalarLagrangian_unitary_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:15:08.221391+00:00
-- url     : https://prove2.me/submissions/30b5b32b-4793-4cf7-a523-e8b1f8c897ad

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs

open Complex

open Complex SMHiggsPotential in
theorem SMHP3de1c97c_normSq_doublet (g M H φ0 : ℝ) (φp : ℂ) :
    doubletNormSq (higgsDoublet g M H φ0 φp) =
      normSq φp + ((vev g M + H) ^ 2 + φ0 ^ 2) / 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [doubletNormSq, higgsDoublet, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [normSq_div, normSq_ofReal, normSq_add_mul_I]
  congr 1
  rw [← sq, h2]

open Complex SMHiggsPotential in
theorem SMHP3de1c97c_formula (g M mh βh H φ0 : ℝ) (φp : ℂ) (hM : M ≠ 0) (hg : g ≠ 0) :
    scalarLagrangian g M mh βh H φ0 φp =
      -βh * doubletNormSq (higgsDoublet g M H φ0 φp)
      - g ^ 2 * alphaH M mh / 2 *
          (doubletNormSq (higgsDoublet g M H φ0 φp) - vev g M ^ 2 / 2) ^ 2
      + 2 * M ^ 4 / g ^ 2 * alphaH M mh := by
  rw [SMHP3de1c97c_normSq_doublet]
  have hmh : mh ^ 2 = 4 * M ^ 2 * alphaH M mh := by
    unfold alphaH; field_simp
  simp only [scalarLagrangian, vev]
  rw [hmh]
  field_simp
  ring

open SMHiggsPotential in
theorem SMHP3de1c97c_norm_unitary (U : Matrix.unitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    doubletNormSq (Matrix.mulVec (U : Matrix (Fin 2) (Fin 2) ℂ) v) = doubletNormSq v := by
  have key : ∀ w : Fin 2 → ℂ, ((doubletNormSq w : ℝ) : ℂ) = star w ⬝ᵥ w := by
    intro w
    simp only [doubletNormSq, dotProduct, Pi.star_apply, ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [normSq_eq_conj_mul_self]; rfl
  apply Complex.ofReal_injective
  rw [key, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hU : Matrix.conjTranspose (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self U
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [hU, Matrix.one_mulVec]

open Complex SMHiggsPotential in
theorem solution (g M mh βh H φ0 H' φ0' : ℝ) (φp φp' : ℂ)
    (hM : M ≠ 0) (hg : g ≠ 0) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (hU : higgsDoublet g M H' φ0' φp' =
      Matrix.mulVec (U : Matrix (Fin 2) (Fin 2) ℂ) (higgsDoublet g M H φ0 φp)) :
    scalarLagrangian g M mh βh H' φ0' φp' = scalarLagrangian g M mh βh H φ0 φp := by
  rw [SMHP3de1c97c_formula _ _ _ _ _ _ _ hM hg, SMHP3de1c97c_formula _ _ _ _ _ _ _ hM hg, hU,
    SMHP3de1c97c_norm_unitary]
