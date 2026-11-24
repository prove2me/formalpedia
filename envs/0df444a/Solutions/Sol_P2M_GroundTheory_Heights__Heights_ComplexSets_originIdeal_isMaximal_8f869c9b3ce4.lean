-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_isMaximal_8f869c9b3ce4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:46.019949+00:00
-- url     : https://prove2.me/submissions/a67717ad-bed8-4b4e-9e49-3cce74d80e0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsConeAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_eq_ker_34d48b0f5439

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (n : ℕ) : (originIdeal n).IsMaximal := by
  rw [originIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, constantCoeff_C _ _⟩)
end GroundTheory.Heights₂.Heights.ComplexSets
