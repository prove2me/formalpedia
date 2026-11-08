-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.qzIncidentFace_card_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:43:16.195391+00:00
-- url     : https://prove2.me/submissions/5eb7a6f0-4884-40ea-b132-96c5fb3fb947

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_qzIncidentFace_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution (P : TannerSquarePresentation)
    (h : BoundedValence P) (e : QZEdge P) :
    Fintype.card (QZIncidentFace P e) ≤ 4 := by
  rw [qzIncidentFace_card]
  exact (h.2.2 e.1.1).1
end QEC.Coding.BDL26BoundedValence
