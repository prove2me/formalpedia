-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.cap_near_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:46:25.823632+00:00
-- url     : https://prove2.me/submissions/201e2176-9a5a-469c-966f-7c69989844a8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (u s : Sphere) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 24)
    (hs : s ∈ cap u (Real.cos θ)) : ‖(s : Space) - (u : Space)‖ ≤ 1 / 8 := by
  have hc : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hi : Real.cos θ ≤ ⟪(u : Space), (s : Space)⟫_ℝ := hs
  have hn := norm_sub_sq_real (s : Space) (u : Space)
  rw [norm_coe, norm_coe] at hn
  have hcomm := real_inner_comm (s : Space) (u : Space)
  have hnorm := norm_nonneg ((s : Space) - (u : Space))
  have hsq : θ ^ 2 ≤ (1 / 24 : ℝ) ^ 2 := by nlinarith
  nlinarith
end QEC.Coding.BDL26RandomPerturbation
