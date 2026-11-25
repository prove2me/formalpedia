-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_C_ff3a58d5ff90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:28.787567+00:00
-- url     : https://prove2.me/submissions/d0916be9-f148-4603-befc-245ef6f066b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_monomial_be73811eb40e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable (K : Type) [Field K] (r : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (c : K) : coneAff K r (C c) = C (algebraMap K _ c) := by
  have h : homMap K r (C c) = C c := by
    rw [← monomial_zero', homMap_monomial, map_zero, monomial_zero']
  simp only [coneAff, RingHom.comp_apply, h, fieldMap, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, sumAlgEquiv_C_inl, map_C]
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin r) K), MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
