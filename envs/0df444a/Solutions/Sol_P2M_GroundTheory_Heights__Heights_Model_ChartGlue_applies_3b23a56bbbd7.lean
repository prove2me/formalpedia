-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_ChartGlue_applies_3b23a56bbbd7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:59.589006+00:00
-- url     : https://prove2.me/submissions/d54107c0-9c74-403d-9a11-76d683efb8f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DominatingDVR_hypotheses_inhabited_a5ce5cb27335
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DominatingDVRScheme_hypotheses_inhabited_e90e44abb2d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BlowUpChart_hypotheses_inhabited_04be7bb79312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_hypotheses_inhabited_dfb5af3f6c1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneIntersection_hypotheses_inhabited_3dd7cb22c212
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_hypotheses_inhabited_2e0532bb94f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hypotheses_inhabited_1f0479b43ccd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadBundle_hypotheses_inhabited_4ad4a2995cf0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadIso_hypotheses_inhabited_370230db64ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_hypotheses_inhabited_1185a6575806
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueBundles_hypotheses_inhabited_d52ffbd2fcda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_ClearDenominators_hypotheses_inhabited_3b7af47caf18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SectionNef_hypotheses_inhabited_9689f7f2198a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SectionNefGenerated_hypotheses_inhabited_6b811562c9e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_MertensUpper_hypotheses_inhabited_408172489351
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SumCp_hypotheses_inhabited_4ffa720a0d9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FiniteIntegralClosure_hypotheses_inhabited_1deaa4585a79
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FiniteNormalization_hypotheses_inhabited_edb5f88a8d5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_hypotheses_inhabited_102eeb634127
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_ChartGlue_hypotheses_inhabited_0ebd25719c21

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
namespace ChartGlue
theorem _root_.solution (h : ChartGlue.Statement) :
    Nonempty (ChartBundle ℤ onePoint 1 (Fin 1 → ℚ)) := by
  let S : Finset Nat.Primes := {⟨2, Nat.prime_two⟩}
  let _ : Algebra (Localization.Away (primeProd S)) ℚ :=
    (awayToRat (primeProd S) (primeProd_ne_zero S)).toAlgebra
  let _ : ∀ p : S, Algebra (ZLoc p) ℚ := fun p => (zLocToRat p).toAlgebra
  obtain ⟨B, -⟩ := h ℚ Unit onePoint 1 (Fin 1 → ℚ) S (Localization.Away (primeProd S))
    (fun p => ZLoc p) (scaledTrivBundle _ onePoint 1 one_ne_zero)
    (fun p => scaledTrivBundle _ onePoint 1 one_ne_zero)
    (fun p i _ => ChartGlue.hypotheses_inhabited S p)
  exact ⟨B⟩
end ChartGlue
end GroundTheory.Heights₂.Heights.Model
