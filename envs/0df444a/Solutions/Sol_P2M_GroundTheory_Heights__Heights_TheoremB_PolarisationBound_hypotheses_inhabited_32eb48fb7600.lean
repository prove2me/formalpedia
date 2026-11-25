-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationBound_hypotheses_inhabited_32eb48fb7600
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:08.027125+00:00
-- url     : https://prove2.me/submissions/812998b6-5457-40de-bb4c-ef3b68855f56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_exists_coeff_bound_f9cc2fcfbccb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace PolarisationBound
theorem _root_.solution (Φ : MvPolynomial (Fin 1) ℝ →ₗ[ℝ] ℝ) :
    ((Finsupp.single (0 : Fin 1) 1).sum fun _ e => e) = 1 ∧
      ∃ M : ℝ, ∀ m', |coeff m' (polarPoly Φ 1)| ≤ M :=
  ⟨Finsupp.sum_single_index rfl, exists_coeff_bound _⟩
end PolarisationBound
end GroundTheory.Heights₂.Heights.TheoremB
