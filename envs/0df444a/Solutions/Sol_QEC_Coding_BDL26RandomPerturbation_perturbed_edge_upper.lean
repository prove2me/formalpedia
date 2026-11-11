-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.perturbed_edge_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:51:17.706888+00:00
-- url     : https://prove2.me/submissions/ea96114a-fcb4-4a74-b5ea-53ba5afff26f

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
    (hp : ‖p‖ = R) (hq : ‖q‖ = R) (hold : ‖a-b‖ ≤ lambda) :
    ‖(a+p)-(b+q)‖ ≤ 2*R+lambda := by
  have he : (a+p)-(b+q) = (a-b)+(p-q) := by abel
  rw [he]
  have h₁ := norm_add_le (a-b) (p-q)
  have h₂ := norm_sub_le p q
  rw [hp,hq] at h₂
  linarith
end QEC.Coding.BDL26RandomPerturbation
