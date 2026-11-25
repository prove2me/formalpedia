-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_rename_eq_symm_comp_C_67f959fd0079
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:07.98211+00:00
-- url     : https://prove2.me/submissions/2de24ebd-72b8-48ff-ac58-e5cb79813d1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_joinPolyEquiv_comp_rename_dddcabe485d5
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
    (rename (R := R) (liftVar (ι := ι) ptIdx)).toRingHom =
      (joinPolyEquiv (R := R) (ι := ι)).symm.toRingHom.comp Polynomial.C := by
  rw [← joinPolyEquiv_comp_rename, ← RingHom.comp_assoc]
  ext x <;> simp
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
