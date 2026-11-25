-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.eJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:22.00817+00:00
-- url     : https://prove2.me/submissions/ccd092ca-14df-4ac2-aff1-134064570900

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_jac

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
    ∏ l : Fin r, (((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
        exp (a i) ^ 2) * (exp γ)⁻¹ ^ ((l : ℕ) + 1)) ^ 2) ^ 2 =
      exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1)) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_jac]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring_nf
  try simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [show ∑ x : Fin r, ((x : ℕ) : ℝ) * γ * 4 = ∑ x : Fin r, γ * ((x : ℕ) : ℝ) * 4 from
    Finset.sum_congr rfl (fun _ _ => by ring)]
  ring
end PI.UnitaryGroupMassFormula.LocJacTyp
