-- Prove2me | solution 1 for PI.OddDualWeyl.Intw.transvection_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:51.548826+00:00
-- url     : https://prove2.me/submissions/629f92b9-38fc-412f-bb94-b3ce445fb847

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
theorem _root_.solution (b a : Fin n) (c : A) (N : Matrix (Fin n) (Fin n) A) (i s : Fin n) :
    (transvection b a c * N) i s = N i s + if i = b then c * N a s else 0 := by
  by_cases h : i = b
  · subst h
    simp [transvection_mul_apply_same]
  · simp [transvection_mul_apply_of_ne, h]
end PI.OddDualWeyl.Intw
