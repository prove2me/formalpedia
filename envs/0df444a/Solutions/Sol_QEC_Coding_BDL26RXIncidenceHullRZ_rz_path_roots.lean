-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullRZ.rz_path_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:25:30.343198+00:00
-- url     : https://prove2.me/submissions/0a4d4662-0746-46bd-b810-fd424c633b02

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRZ_rz_same_q
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRZ_rz_shared_roots
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_trans
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullRZ
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RXIncidenceHullGrowth
open scoped Classical
namespace QEC.Coding.BDL26RXIncidenceHullRZ
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) {q r : P.Q} (path : SharedZPath P q r) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rzReplacementPresentation P A S) (rzRoot P A S q a) (rzRoot P A S r b) := by
  have same : SharedZPath (rzReplacementPresentation P A S) (rzRoot P A S q a) (rzRoot P A S r a) := by
    induction path with
    | refl => exact .refl _
    | snoc path z left right ih => exact ih.trans (rz_shared_roots P A S _ _ z left right a)
  exact same.trans (rz_same_q P A S r a b)
end QEC.Coding.BDL26RXIncidenceHullRZ
