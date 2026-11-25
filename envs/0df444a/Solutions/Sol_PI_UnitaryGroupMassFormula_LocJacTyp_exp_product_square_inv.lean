-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.exp_product_square_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:45.507301+00:00
-- url     : https://prove2.me/submissions/f4b346a3-e59e-493c-9c6a-fd9c519786b4

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
theorem _root_.solution (a : Fin (r + 1) → ℝ) :
    ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((exp (a i) * exp (a j)) ^ 2)⁻¹ =
      exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_neg_distrib, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.LocJacTyp
