-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.qzIncidentFace_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:39:14.897269+00:00
-- url     : https://prove2.me/submissions/99535125-bf2a-4922-8149-9e33fc0516e3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_qzIncidentFace_to_x_bijective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution (P : TannerSquarePresentation) (e : QZEdge P) :
    Fintype.card (QZIncidentFace P e) = qXDegree P e.1.1 := by
  classical
  exact Fintype.card_of_bijective (qzIncidentFace_to_x_bijective P e)
end QEC.Coding.BDL26BoundedValence
