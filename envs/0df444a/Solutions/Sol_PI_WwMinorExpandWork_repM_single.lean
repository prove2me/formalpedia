-- Prove2me | solution 1 for PI.WwMinorExpandWork.repM_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:08.274271+00:00
-- url     : https://prove2.me/submissions/87175656-a488-456a-8d83-234cd8c57ad8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMinorExpand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorExpansion_WwMinorExpandMain

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
open PI PI.WwMinorExpandWork
open PI.WwMinorExpand
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)
namespace PI.WwMinorExpandWork
theorem _root_.solution (s : Lt) (p : ℕ) (J : Fin p ↪o Fin N0) (c : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) :
    RepM N0 N1 s p (MvPolynomial.rename Sum.inl (minX N0 s p J) * MvPolynomial.rename Sum.inr c) := by
  classical
  refine ⟨fun J' => if J' = J then c else 0, ?_⟩
  simp only [apply_ite, map_zero, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end PI.WwMinorExpandWork
