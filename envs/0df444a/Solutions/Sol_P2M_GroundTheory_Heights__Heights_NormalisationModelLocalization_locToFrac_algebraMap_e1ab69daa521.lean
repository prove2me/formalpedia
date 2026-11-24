-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_algebraMap_e1ab69daa521
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:59.02304+00:00
-- url     : https://prove2.me/submissions/fbd59d47-6b60-4701-983d-2db47750a5f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX

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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalisationModelLocalization
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
variable {M}
variable (M)
namespace GroundTheory.Heights₂.Heights.NormalisationModelLocalization
theorem _root_.solution (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (r : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :
    locToFrac M hJ hq (algebraMap _ _ r) = modelToFrac M hJ hq r := by
  rw [locToFrac]
  exact IsLocalization.lift_eq _ _
end GroundTheory.Heights₂.Heights.NormalisationModelLocalization
