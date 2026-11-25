-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_map_eq_c75b8e5ef470
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:05.041984+00:00
-- url     : https://prove2.me/submissions/67111590-7b82-41aa-820a-b453508649a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDedekindFibreRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
open scoped Pointwise
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {N : ℕ}
    (d : ℕ) (p : Poly R N) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.Kleiman
