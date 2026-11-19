-- Prove2me | solution 1 for Plasticity.C0Sum.not_hasPlasticUnitBall_ell1_c0
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T19:27:15.330138+00:00
-- url     : https://prove2.me/submissions/a3388916-cb87-436e-90ec-f63d90369fc5

import Mathlib.Analysis.Real.Cardinality
import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_SeqSpace
import Definitions.Def_Plasticity_C0Sum
import Theorems.Thm_Plasticity_C0Sum_not_hasPlasticUnitBall_of_ball_map
import Theorems.Thm_Plasticity_Ell1C0_exists_bijective_ball_map

namespace Sol_Plasticity_C0Sum_not_hasPlasticUnitBall_ell1_c0
end Sol_Plasticity_C0Sum_not_hasPlasticUnitBall_ell1_c0

open Plasticity in
theorem solution :
    ¬ HasPlasticUnitBall
      (c0Sum (fun _ : ℕ => lp (fun _ : ℝ => ℝ) 1) × c0Sum (fun _ : ℕ => c0 ℝ)) := by
  obtain ⟨F, hF, hbij, h0, u, hu⟩ := Ell1C0.exists_bijective_ball_map ℝ Cardinal.mk_real
  refine C0Sum.not_hasPlasticUnitBall_of_ball_map F hF hbij ?_
  intro hiso
  obtain ⟨h1, h2⟩ := hu 0
  have := hiso.dist_eq ⟨0, Metric.mem_closedBall_self zero_le_one⟩ (u 0)
  rw [h0] at this
  have e1 : dist (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Metric.closedBall (0 : lp (fun _ : ℝ => ℝ) 1) 1) (u 0) = 1 := by
    rw [Subtype.dist_eq, dist_eq_norm]; simpa [norm_sub_rev] using h1
  have e2 : dist (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Metric.closedBall (0 : c0 ℝ) 1) (F (u 0)) = 1/2 := by
    rw [Subtype.dist_eq, dist_eq_norm]; simp [norm_sub_rev] at h2 ⊢; simpa using h2
  rw [e1, e2] at this
  norm_num at this
