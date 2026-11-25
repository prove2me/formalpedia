-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.sum_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:58.676433+00:00
-- url     : https://prove2.me/submissions/4013e549-529f-4bc9-982d-7f042e23eb30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_le__26af5c2b73f2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (r : ℕ) (a : Fin (r + 1) → ℝ) :
    ∑ l : Fin r, ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), a i =
      ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_le']
end PI.UnitaryGroupMassFormula.LocJacTyp
