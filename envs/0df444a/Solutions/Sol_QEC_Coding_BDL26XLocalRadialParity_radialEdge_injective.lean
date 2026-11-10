-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalRadialParity.radialEdge_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:33:08.776247+00:00
-- url     : https://prove2.me/submissions/b8cdec7e-c5c9-4e18-b551-063cb274648e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical
namespace QEC.Coding.BDL26XLocalRadialParity
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X) :
    Function.Injective (radialEdge P A x) := by
  intro q r h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  have hp := Sum.inl.inj he
  exact congrArg (fun e : XQEdge P => e.val.2) hp
end QEC.Coding.BDL26XLocalRadialParity
