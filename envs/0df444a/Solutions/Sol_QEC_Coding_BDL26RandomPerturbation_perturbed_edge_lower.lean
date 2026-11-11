-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.perturbed_edge_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:50:39.982246+00:00
-- url     : https://prove2.me/submissions/53cf8d75-3644-4841-b2da-ec371b455e09

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a b p q : E) {R lambda : ℝ}
    (hchord : R ≤ ‖p-q‖) (hold : ‖a-b‖ ≤ lambda) :
    R-lambda ≤ ‖(a+p)-(b+q)‖ := by
  have he : p-q = ((a+p)-(b+q))-(a-b) := by abel
  have h := norm_sub_le ((a+p)-(b+q)) (a-b)
  rw [← he] at h
  linarith
end QEC.Coding.BDL26RandomPerturbation
