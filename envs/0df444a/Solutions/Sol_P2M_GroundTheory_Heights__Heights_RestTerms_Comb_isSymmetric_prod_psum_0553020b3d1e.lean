-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isSymmetric_prod_psum_0553020b3d1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:23.494797+00:00
-- url     : https://prove2.me/submissions/000248f4-93dd-4cd7-b714-1b2937811de0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (ρ : List ℕ) :
    ((ρ.map fun q => psum (Fin m) ℚ q).prod).IsSymmetric := by
  induction ρ with
  | nil => simp only [List.map_nil, List.prod_nil]; exact IsSymmetric.one
  | cons q ρ ih => simpa using (psum_isSymmetric (Fin m) ℚ q).mul ih
end GroundTheory.Heights₂.Heights.RestTerms.Comb
