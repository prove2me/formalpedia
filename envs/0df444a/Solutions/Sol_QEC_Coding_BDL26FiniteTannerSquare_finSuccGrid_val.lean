-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.finSuccGrid_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:39:31.390833+00:00
-- url     : https://prove2.me/submissions/7dcbeeca-6f79-4b48-9cc8-5f3860013bfd

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
theorem _root_.solution {m : Nat} (i : Fin m) :
    (finSuccGrid i).1 = i.1 + 1 := rfl
end QEC.Coding.BDL26FiniteTannerSquare
