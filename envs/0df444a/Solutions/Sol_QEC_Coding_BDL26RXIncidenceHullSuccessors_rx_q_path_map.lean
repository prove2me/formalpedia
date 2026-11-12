-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_path_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:24:45.495405+00:00
-- url     : https://prove2.me/submissions/8e834957-ba8b-4b21-ae53-53d566d3408c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_start_incidence
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_end_incidence

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth
namespace QEC.Coding.BDL26RXIncidenceHullSuccessors
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    {u v : QDoubleCylinderVertex P q S}
    (path : UndirectedPath (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) u v) :
    SharedZPath (rxReplacementPresentation P S) (Sum.inr ⟨q,u⟩) (Sum.inr ⟨q,v⟩) := by
  induction path with
  | nil => exact .refl _
  | @step u v path edge connects ih =>
      rcases connects with ⟨hs,he⟩ | ⟨hs,he⟩
      · exact .snoc ih (Sum.inl (Sum.inr ⟨q,edge⟩))
          (hs ▸ rx_q_start_incidence P A S q edge)
          (he ▸ rx_q_end_incidence P A S q edge)
      · exact .snoc ih (Sum.inl (Sum.inr ⟨q,edge⟩))
          (he ▸ rx_q_end_incidence P A S q edge)
          (hs ▸ rx_q_start_incidence P A S q edge)
end QEC.Coding.BDL26RXIncidenceHullSuccessors
