-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.subdivisionBoundaryEdgeStart_ne_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:37:38.20771+00:00
-- url     : https://prove2.me/submissions/932fc561-abe9-410d-83a9-7b1d8c4b9585

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionEdgeStart_ne_end

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
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionBoundaryEdge P x S) :
    subdivisionBoundaryEdgeStart P x S edge ≠
      subdivisionBoundaryEdgeEnd P x S edge := by
  intro h
  have hvalue := congrArg Subtype.val h
  rw [subdivisionBoundaryEdgeStart_value,
    subdivisionBoundaryEdgeEnd_value] at hvalue
  exact subdivisionEdgeStart_ne_end P x S edge.1 hvalue
end QEC.Coding.BDL26FiniteTannerSquare
