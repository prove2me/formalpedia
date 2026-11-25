-- Prove2me | solution 1 for PI.WwMinorExpandWork.repM_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:15:46.236257+00:00
-- url     : https://prove2.me/submissions/7cf9cacc-6528-42a9-b104-697ecdaf671b

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
theorem _root_.solution (s : Lt) (p : ℕ) {x y : MvPolynomial (KM.XZ Lt N0 N1) ℤ}
    (hx : RepM N0 N1 s p x) (hy : RepM N0 N1 s p y) : RepM N0 N1 s p (x + y) := by
  obtain ⟨d, rfl⟩ := hx
  obtain ⟨e, rfl⟩ := hy
  refine ⟨d + e, ?_⟩
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end PI.WwMinorExpandWork
