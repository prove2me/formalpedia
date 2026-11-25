-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.eU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:41.405929+00:00
-- url     : https://prove2.me/submissions/4a18a380-56ee-4c0e-9bb8-a4826a3aec39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_fst
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_snd

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
    ∏ q : UIdx r, (exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) =
      exp (2 * γ * (Fintype.card (UIdx r) : ℝ) + 4 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_sum]
  congr 1
  rw [← sum_fst r a, ← sum_snd r a]
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.LocJacTyp
