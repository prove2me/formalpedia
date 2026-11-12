-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.legacy_bounded_specialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:08:12.281933+00:00
-- url     : https://prove2.me/submissions/8a19ec1d-4d0e-4f41-b39f-b9a366fa27ba

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
variable (P : TannerSquarePresentation) (key : Triangle P → ℕ)
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (hv : BoundedValence P) (t : Triangle P) :
    boundedPolicyColor P (triangleKey P) hv t=boundedTriangleColor P hv t := by
  funext i
  apply Fin.ext
  rfl
end QEC.Coding.BDL26NativeTriangleColors
