-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.entry_bound_block_matrix_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:13.997772+00:00
-- url     : https://prove2.me/submissions/3b7f599d-9369-42d2-bedb-d80717e75fde

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Ux5
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {p s : ℕ} {A : Matrix (Fin p) (Fin p) ℂ} {B' : Matrix (Fin p) (Fin s) ℂ}
    {C' : Matrix (Fin s) (Fin p) ℂ} {D : Matrix (Fin s) (Fin s) ℂ} {c : ℝ}
    (hA : EB A c) (hB : EB B' c) (hC : EB C' c) (hD : EB D c) : EB (blk2 A B' C' D) c := by
  intro i j
  show ‖fromBlocks A B' C' D (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)‖ ≤ c
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b
  · exact hA a b
  · exact hB a b
  · exact hC a b
  · exact hD a b
end PI.UnitaryGroupMassFormula.UsCost
