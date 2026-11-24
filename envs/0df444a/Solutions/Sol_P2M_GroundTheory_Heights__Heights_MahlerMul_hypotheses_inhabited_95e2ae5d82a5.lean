-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerMul_hypotheses_inhabited_95e2ae5d82a5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:29.480389+00:00
-- url     : https://prove2.me/submissions/953a1c31-089f-466a-a3fa-80a7260f5a1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace MahlerMul
theorem _root_.solution :
    (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℂ) ≠ 0 ∧ (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℂ) ≠ 0 :=
  ⟨X_ne_zero _, X_ne_zero _⟩
end MahlerMul
end GroundTheory.Heights₂.Heights
