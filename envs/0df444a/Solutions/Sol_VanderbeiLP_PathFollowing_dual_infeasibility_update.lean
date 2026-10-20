-- Prove2me | solution 1 for VanderbeiLP.PathFollowing.dual_infeasibility_update
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:50:31.057959+00:00
-- url     : https://prove2.me/submissions/492a3c1b-fa1d-4edd-8cfa-af3e0fc2b168

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
    dualInfeas A c p' = (1 - stepLength r p d) • dualInfeas A c p := by
  rcases hstep with ⟨_, ⟨_, hdual, _, _⟩, hnext⟩
  set θ := stepLength r p d
  rw [hnext]
  ext j
  have hj := congrFun hdual j
  simp [dualInfeas] at hj
  simp [dualInfeas, PDPoint.advance, Matrix.mulVec_add, Matrix.mulVec_smul, θ]
  linear_combination -θ * hj
