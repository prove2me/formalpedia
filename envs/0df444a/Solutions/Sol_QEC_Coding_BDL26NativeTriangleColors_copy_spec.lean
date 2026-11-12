-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.copy_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:08:50.249743+00:00
-- url     : https://prove2.me/submissions/443fae65-46da-468f-b21c-a1479e379770

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (c : Code) :
    (copyCodeQ c).value=c ∧ (copyCodeQ c).operations=21 ∧ (copyCodeQ c).allocations=1 :=
  ⟨rfl,rfl,rfl⟩
end QEC.Coding.BDL26NativeTriangleColors
