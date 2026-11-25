-- Prove2me | solution 1 for PI.QmRowExpWork.sign_extend_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:47.333564+00:00
-- url     : https://prove2.me/submissions/5bc8708d-e0c0-44e1-a92e-28a41868bc1b

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
theorem _root_.solution {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ext0 τ) = Equiv.Perm.sign τ := by
  rw [ext0, Equiv.Perm.sign_trans_trans_symm, Equiv.optionCongr_sign]
end PI.QmRowExpWork
