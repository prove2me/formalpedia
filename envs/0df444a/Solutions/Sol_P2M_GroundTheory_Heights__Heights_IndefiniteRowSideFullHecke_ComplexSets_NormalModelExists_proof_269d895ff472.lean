-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelExists_proof_269d895ff472
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:53:32.171542+00:00
-- url     : https://prove2.me/submissions/84ae4ec7-2c80-457a-ae1b-ab4d6b77bc8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NonemptyNormalModelOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_nonempty_normalModel_of_presentation_27235b04eeff
import Theorems.Thm_UpperTheory_Reformulated_B_Gc5_nonempty_normalModel_of_presentation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalModelExists
theorem _root_.solution : NormalModelExists.Statement := by
  intro n J hJ
  exact nonempty_normalModel_of_presentation J (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mkₐ ℂ J)
    (Ideal.Quotient.mkₐ_surjective ℂ J) (Ideal.Quotient.mkₐ_ker ℂ J)
end NormalModelExists
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
