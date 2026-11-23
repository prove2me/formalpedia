-- Prove2me | solution 1 for PI.QmSandwichWork.tm_entry_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:19.238554+00:00
-- url     : https://prove2.me/submissions/fce89fd2-c8fc-4d1f-a439-400b42ef9ef6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_RttRelation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EntrywiseSandwichCommute_BlockEmbeddingMulEntrySwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmSandwichWork
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P.W
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace PI.QmSandwichWork
theorem _root_.solution (Y : ℂ) {p c ci x : A} (hp : Commute p x) (hc : Commute c x)
    (hci : Commute ci x) (i j : Fin 2) : Commute (Tm Y p c ci i j) x := by
  fin_cases i <;> fin_cases j
  · simpa [Tm] using (Algebra.commute_algebraMap_left Y x).add_left hp
  · simpa [Tm] using hc.neg_left
  · simpa [Tm] using hci
  · simp [Tm]
end PI.QmSandwichWork
