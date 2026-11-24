-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:29.426175+00:00
-- url     : https://prove2.me/submissions/61e62ef4-aa9c-48c4-88b2-b52af1872b15

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
namespace ChowHeightMul
theorem _root_.solution :
    (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℚ) ≠ 0 ∧ (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℚ) ≠ 0 :=
  ⟨X_ne_zero _, X_ne_zero _⟩
end ChowHeightMul
end GroundTheory.Heights₂.Heights
