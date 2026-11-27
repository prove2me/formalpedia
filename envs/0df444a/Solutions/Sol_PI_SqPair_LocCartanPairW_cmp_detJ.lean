-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_detJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:16:41.487839+00:00
-- url     : https://prove2.me/submissions/e5088f5f-7060-4c27-8f0c-9833dd806b05

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock

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
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution [Nontrivial R] : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  simp
end PI.SqPair.LocCartanPairW
