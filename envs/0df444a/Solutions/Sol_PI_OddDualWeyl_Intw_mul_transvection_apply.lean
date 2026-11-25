-- Prove2me | solution 1 for PI.OddDualWeyl.Intw.mul_transvection_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:46.006833+00:00
-- url     : https://prove2.me/submissions/746607a4-7cc2-453c-9edc-b1abd767b674

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply

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
open PI.OddDualWeyl.Intw
variable {A : Type*} [CommRing A] {n : ℕ}
namespace PI.OddDualWeyl.Intw
theorem _root_.solution (b a : Fin n) (c : A) (N : Matrix (Fin n) (Fin n) A) (p i : Fin n) :
    (N * transvection b a c) p i = N p i + if i = a then N p b * c else 0 := by
  by_cases h : i = a
  · subst h
    rw [mul_transvection_apply_same, if_pos rfl]
    ring
  · simp [mul_transvection_apply_of_ne, h]
end PI.OddDualWeyl.Intw
