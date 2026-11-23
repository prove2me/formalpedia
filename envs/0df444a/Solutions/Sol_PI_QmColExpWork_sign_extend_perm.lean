-- Prove2me | solution 1 for PI.QmColExpWork.sign_extend_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:11.683022+00:00
-- url     : https://prove2.me/submissions/61bbac66-6e72-49a4-ab67-c09b80f3e7b5

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective

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
open PI PI.QmColExpWork
open Formalism.REAL
namespace PI.QmColExpWork
theorem _root_.solution {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ext0 τ) = Equiv.Perm.sign τ := by
  unfold ext0
  first
  | exact (Equiv.Perm.sign_symm_trans_trans _ _).trans (Equiv.optionCongr_sign τ)
  | exact (Equiv.Perm.sign_permCongr _ _).trans (Equiv.optionCongr_sign τ)
end PI.QmColExpWork
