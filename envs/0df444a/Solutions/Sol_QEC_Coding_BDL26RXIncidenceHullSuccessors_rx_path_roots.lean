-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_path_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:15:25.797591+00:00
-- url     : https://prove2.me/submissions/bbb46d83-3827-40de-a52d-6d6f9ddbd2f8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_cylinder_connected
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_shared_z_roots
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_trans
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth
namespace QEC.Coding.BDL26RXIncidenceHullSuccessors
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) {q r : P.Q} (path : SharedZPath P q r) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rxReplacementPresentation P S) (rxRoot P S q a) (rxRoot P S r b) := by
  induction path generalizing a b with
  | refl => exact rx_q_cylinder_connected P A S _ _ _
  | @snoc r t path z left right ih =>
      exact (ih a 0).trans (rx_shared_z_roots P A S r t z left right 0 b)
end QEC.Coding.BDL26RXIncidenceHullSuccessors
