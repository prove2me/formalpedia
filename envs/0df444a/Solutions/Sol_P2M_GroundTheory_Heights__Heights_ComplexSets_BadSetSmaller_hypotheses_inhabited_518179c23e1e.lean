-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_BadSetSmaller_hypotheses_inhabited_518179c23e1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:29:10.404272+00:00
-- url     : https://prove2.me/submissions/4af58034-aa33-4c0a-97dd-c1e5dcd9b569

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_hyps_b9b793686593

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
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace BadSetSmaller
theorem _root_.solution :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧ (X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 :=
  ⟨cone_hyps, X_ne_zero _⟩
end BadSetSmaller
end GroundTheory.Heights₂.Heights.ComplexSets
