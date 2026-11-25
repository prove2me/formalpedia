-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_line_dim_69b0ee92cc8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:39.363664+00:00
-- url     : https://prove2.me/submissions/c626f6d2-5da7-4f9d-92f5-2f4e0f2c43e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements

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
theorem _root_.solution : ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) =
    (1 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
end GroundTheory.Heights₂.Heights.ComplexSets
