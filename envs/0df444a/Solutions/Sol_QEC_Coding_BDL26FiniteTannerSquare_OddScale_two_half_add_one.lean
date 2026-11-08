-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.OddScale.two_half_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:39:05.342043+00:00
-- url     : https://prove2.me/submissions/f905fc6e-15cc-4009-bf74-f91a3e5df143

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open BDL26FiniteAlternatingCore
open Module
attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq
namespace QEC.Coding.BDL26FiniteTannerSquare
namespace OddScale
theorem _root_.solution (S : OddScale) : 2 * S.half + 1 = S.ell := by
  have hodd := S.odd
  unfold OddScale.half
  omega
end OddScale
end QEC.Coding.BDL26FiniteTannerSquare
