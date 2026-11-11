-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.widthFactor_le_three_quarters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:50:11.300204+00:00
-- url     : https://prove2.me/submissions/df4e107b-e141-4148-bd5c-07fce81e409a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution : widthFactor ≤ 3/4 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := (1 : ℝ)/6)
  unfold widthFactor
  linarith
end QEC.Coding.BDL26RandomPerturbation
