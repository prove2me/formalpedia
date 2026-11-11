-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.cap_pair_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:50:53.233753+00:00
-- url     : https://prove2.me/submissions/69a1c955-c7d2-455f-b93d-2f188e8ef527

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_cap_near_axis

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (u v s t : Sphere) (huv : ⟪(u : Space), (v : Space)⟫_ℝ = 0)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 24)
    (hs : s ∈ cap u (Real.cos θ)) (ht : t ∈ cap v (Real.cos θ)) :
    ⟪(s : Space), (t : Space)⟫_ℝ ≤ 1 / 4 := by
  have hs' := cap_near_axis u s hθ0 hθ1 hs
  have ht' := cap_near_axis v t hθ0 hθ1 ht
  have h₁ := real_inner_le_norm ((s : Space) - (u : Space)) (t : Space)
  have h₂ := real_inner_le_norm (u : Space) ((t : Space) - (v : Space))
  rw [norm_coe, mul_one, inner_sub_left] at h₁
  rw [norm_coe, one_mul, inner_sub_right, huv] at h₂
  linarith
end QEC.Coding.BDL26RandomPerturbation
