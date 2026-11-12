-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.legacy_specialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:08:00.085262+00:00
-- url     : https://prove2.me/submissions/d6283664-a031-4cb1-86b8-467b2711f07e

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
theorem _root_.solution (t : Triangle P) :
    policyColor P (triangleKey P) t=triangleColor P t := rfl
end QEC.Coding.BDL26NativeTriangleColors
