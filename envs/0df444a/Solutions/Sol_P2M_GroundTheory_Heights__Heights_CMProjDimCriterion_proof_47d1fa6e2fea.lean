-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CMProjDimCriterion_proof_47d1fa6e2fea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:06:00.11166+00:00
-- url     : https://prove2.me/submissions/4f276612-3638-4f01-8da2-b44be926d269

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMProjDimCriterion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing_3eacb56911f2
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_localization_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory RingTheory.Sequence
namespace GroundTheory.Heights₂.Heights
namespace CMProjDimCriterion
theorem _root_.solution (hlow : AuslanderBuchsbaumDepthLower.Statement.{0})
    (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0}) (hlen : RegularSequenceLengthLeDim.Statement.{0})
    (hcm : CMHeightAddDim.Statement.{0}) : CMProjDimCriterion.Statement := by
  intro n I Q _ hIQ
  have : Algebra.Smooth ℂ (MvPolynomial (Fin n) ℂ) := {}
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth ℂ (MvPolynomial (Fin n) ℂ) Q
  refine isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing hlow hup hlen hcm _ ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono hIQ
end CMProjDimCriterion
end GroundTheory.Heights₂.Heights
