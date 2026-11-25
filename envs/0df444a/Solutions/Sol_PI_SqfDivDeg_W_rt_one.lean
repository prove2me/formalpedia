-- Prove2me | solution 1 for PI.SqfDivDeg.W.rt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:26.53926+00:00
-- url     : https://prove2.me/submissions/19e5d8d0-9e08-4a7a-8077-7f69cc3c34b5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
import Theorems.Thm_PI_SqfDivDeg_W_mem_Mon


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical
namespace PI.SqfDivDeg.W
theorem _root_.solution (g : ℕ) [Fact g.Prime] : Rt g 1 = Mon g 1 := by
  unfold Rt
  apply Finset.filter_true_of_mem
  intro p hp
  rw [mem_Mon] at hp
  exact exists_root_of_degree_eq_one
    (by rw [degree_eq_natDegree hp.1.ne_zero, hp.2, Nat.cast_one])
end PI.SqfDivDeg.W
