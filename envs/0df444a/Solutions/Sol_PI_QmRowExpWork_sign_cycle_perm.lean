-- Prove2me | solution 1 for PI.QmRowExpWork.sign_cycle_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:42.658376+00:00
-- url     : https://prove2.me/submissions/f3b36569-da60-4b95-8035-b8c736057a2b

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmRowExpWork
open Formalism.REAL
namespace PI.QmRowExpWork
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) :
    Equiv.Perm.sign (cyc0 m j) = (-1) ^ (j : ℕ) := by
  rw [cyc0, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
end PI.QmRowExpWork
