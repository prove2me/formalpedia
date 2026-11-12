-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_cylinder_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:57:25.391685+00:00
-- url     : https://prove2.me/submissions/e1f29e42-dcb8-49f3-9e2b-ca7012fabc32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_path_map
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_symm
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_trans
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth
namespace QEC.Coding.BDL26RXIncidenceHullSuccessors
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (u v : QDoubleCylinderVertex P q S) :
    SharedZPath (rxReplacementPresentation P S) (Sum.inr ⟨q,u⟩) (Sum.inr ⟨q,v⟩) :=
  (rx_q_path_map P A S q (qDoubleCylinderPath P A q S u)).symm.trans
    (rx_q_path_map P A S q (qDoubleCylinderPath P A q S v))
end QEC.Coding.BDL26RXIncidenceHullSuccessors
