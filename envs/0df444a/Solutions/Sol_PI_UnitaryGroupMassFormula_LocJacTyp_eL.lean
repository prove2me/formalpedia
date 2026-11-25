-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.eL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:50.520219+00:00
-- url     : https://prove2.me/submissions/2bf4cfd8-599a-4eb3-9e3a-47f4e14f2dd9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv

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
open Real
variable (r : ℕ)
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ l : Fin (r + 1), (exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) =
      exp (3 * ((r : ℝ) + 1) * γ - 4 * ∑ l, a l) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.LocJacTyp
