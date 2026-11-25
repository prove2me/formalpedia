-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_joinPolyEquiv_comp_rename_dddcabe485d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:57.753631+00:00
-- url     : https://prove2.me/submissions/bb129db6-ad3f-4e1a-899a-417347717276

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
theorem _root_.solution :
    (joinPolyEquiv (R := R) (ι := ι)).toRingHom.comp (rename (R := R) (liftVar (ι := ι) ptIdx)).toRingHom =
      Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [joinPolyEquiv, optionEquivLeft_C]
  · intro p
    simp [joinPolyEquiv, joinIdxEquiv, liftVar, optionEquivLeft_X_some]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
