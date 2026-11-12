-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_shared_z_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:08:13.774554+00:00
-- url     : https://prove2.me/submissions/a721218b-8e56-4709-909a-a070d5fe8b4b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_cylinder_connected
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_old_z_incidence
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
    (S : OddScale) (q r : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (hrz : P.qz r z = true) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rxReplacementPresentation P S) (rxRoot P S q a) (rxRoot P S r b) := by
  let u : QDoubleCylinderVertex P q S := (0,Sum.inl (Sum.inr ⟨z,hqz⟩))
  let v : QDoubleCylinderVertex P r S := (0,Sum.inl (Sum.inr ⟨z,hrz⟩))
  have first := rx_q_cylinder_connected P A S q (a,Sum.inl (Sum.inl ())) u
  have middle : SharedZPath (rxReplacementPresentation P S)
      (Sum.inr ⟨q,u⟩) (Sum.inr ⟨r,v⟩) :=
    .snoc (.refl _) (Sum.inr (z,0)) (rx_old_z_incidence P A S q z hqz)
      (rx_old_z_incidence P A S r z hrz)
  exact first.trans (middle.trans
    (rx_q_cylinder_connected P A S r v (b,Sum.inl (Sum.inl ()))))
end QEC.Coding.BDL26RXIncidenceHullSuccessors
