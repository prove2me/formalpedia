-- Prove2me | solution 1 for PI.SwBig.PhiFormProof.exp_neg_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:55.493539+00:00
-- url     : https://prove2.me/submissions/87808fad-15a3-4994-a9ca-dc293fcd5efa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiBigCellForm_BigCellEqW0BMulTM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.PhiFormProof
open PI.SwBig
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
namespace PI.SwBig.PhiFormProof
theorem _root_.solution (k r : ℕ) (X : Mat k r) :
    NormedSpace.exp (-X) = (NormedSpace.exp X)⁻¹ :=
  Matrix.exp_neg X
end PI.SwBig.PhiFormProof
