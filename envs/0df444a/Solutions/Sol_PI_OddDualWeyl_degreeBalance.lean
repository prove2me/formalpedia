-- Prove2me | solution 1 for PI.OddDualWeyl.degreeBalance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:50.496834+00:00
-- url     : https://prove2.me/submissions/801b7bb8-1678-4f09-bfa2-e13acf783c01

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DegreeBalance
import Theorems.Thm_PI_OddDualWeyl_MiscB_degW_eq
import Theorems.Thm_PI_OddDualWeyl_MiscB_nu_cast
import Theorems.Thm_PI_OddDualWeyl_MiscB_nu_anti
import Theorems.Thm_PI_OddDualWeyl_MiscB_sum_nu_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
namespace PI.OddDualWeyl
theorem _root_.solution : Bk := by
  intro m lam hl
  have hs : Antitone (lamStar lam) := fun i j hij => by
    unfold lamStar
    exact neg_le_neg (hl (Fin.rev_le_rev.2 hij))
  unfold expM
  rw [MiscB.degW_eq _ (MiscB.nu_anti hs), Nat.cast_sub (MiscB.sum_nu_le hl)]
  push_cast
  simp only [MiscB.nu_cast hs, MiscB.nu_cast hl]
  have hr : ∑ t : Fin (m + 1), (lamStar lam t - lamStar lam (Fin.last m)) =
      ∑ t : Fin (m + 1), (lam 0 - lam t) := by
    unfold lamStar
    rw [Fin.rev_last, ← Equiv.sum_comp Fin.revPerm (fun t => lam 0 - lam t)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Fin.revPerm_apply]
    ring
  rw [hr]
  unfold lamStar
  rw [Fin.rev_last]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
end PI.OddDualWeyl
