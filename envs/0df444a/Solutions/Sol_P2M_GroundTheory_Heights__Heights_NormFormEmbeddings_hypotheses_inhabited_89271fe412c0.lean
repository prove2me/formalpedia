-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormFormEmbeddings_hypotheses_inhabited_89271fe412c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:13.280873+00:00
-- url     : https://prove2.me/submissions/f891c583-8a79-4ef6-89a9-61445f7f4003

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NormFormEmbeddings
theorem _root_.solution :
    Infinite ℚ ∧ FiniteDimensional ℚ ℚ ∧ Algebra.IsSeparable ℚ ℚ ∧ IsAlgClosed (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
end NormFormEmbeddings
end GroundTheory.Heights₂.Heights
