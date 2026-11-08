-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.xqIncidentFace_card_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:43:04.167981+00:00
-- url     : https://prove2.me/submissions/74ee97ba-2ee1-4285-b2fc-df739d9e19b6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_xqIncidentFace_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution (P : TannerSquarePresentation)
    (h : BoundedValence P) (e : XQEdge P) :
    Fintype.card (XQIncidentFace P e) ≤ 4 := by
  rw [xqIncidentFace_card]
  exact (h.2.2 e.1.2).2.1
end QEC.Coding.BDL26BoundedValence
