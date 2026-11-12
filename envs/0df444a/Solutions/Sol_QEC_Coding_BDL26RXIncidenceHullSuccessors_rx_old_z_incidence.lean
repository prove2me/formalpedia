-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_old_z_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:17:05.700428+00:00
-- url     : https://prove2.me/submissions/c9333e0d-d04e-4f82-80a2-beadbfd76123

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_old_qz_face

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth
namespace QEC.Coding.BDL26RXIncidenceHullSuccessors
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q,(0,Sum.inl (Sum.inr (⟨z,hqz⟩ : QStarEdge P q)))⟩)
      (Sum.inr (z,0)) = true := by
  obtain ⟨f,corner,hq,hz⟩ := old_qz_face P A q z hqz
  subst q
  subst z
  let face : RXFace P S := Sum.inr (Sum.inr (f,0))
  apply (rxQZIncidence_eq_true_iff P S _ _).mpr
  refine ⟨face,corner,?_,?_⟩
  · rfl
  · rfl
end QEC.Coding.BDL26RXIncidenceHullSuccessors
