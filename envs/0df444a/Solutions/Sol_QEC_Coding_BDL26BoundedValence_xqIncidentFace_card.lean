-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.xqIncidentFace_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:39:37.729212+00:00
-- url     : https://prove2.me/submissions/127e79e3-d3f2-4706-9669-6764e7ebaac7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_xqIncidentFace_to_z_bijective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution (P : TannerSquarePresentation) (e : XQEdge P) :
    Fintype.card (XQIncidentFace P e) = qZDegree P e.1.2 := by
  classical
  exact Fintype.card_of_bijective (xqIncidentFace_to_z_bijective P e)
end QEC.Coding.BDL26BoundedValence
