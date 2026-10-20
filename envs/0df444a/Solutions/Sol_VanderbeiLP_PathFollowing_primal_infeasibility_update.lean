-- Prove2me | solution 1 for VanderbeiLP.PathFollowing.primal_infeasibility_update
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:48:00.603102+00:00
-- url     : https://prove2.me/submissions/0a4f0999-fc7e-455a-87fb-0fdd17b58b20

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open VanderbeiLP.PathFollowing

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r < 1) (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p') :
    primalInfeas A b p' = (1 - stepLength r p d) • primalInfeas A b p := by
  rcases hstep with ⟨_, hdir, hnext⟩
  have hprimal := hdir.1
  simp [primalInfeas] at hprimal
  set θ := stepLength r p d
  rw [hnext]
  simp [primalInfeas, PDPoint.advance, Matrix.mulVec_add, Matrix.mulVec_smul, θ]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hpi := congrFun hprimal i
  simp [primalInfeas] at hpi
  linear_combination -θ * hpi
