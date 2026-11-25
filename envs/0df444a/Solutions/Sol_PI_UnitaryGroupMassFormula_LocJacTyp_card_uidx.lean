-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.card_uidx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:48.87941+00:00
-- url     : https://prove2.me/submissions/6cdf7de0-923a-4ccf-b359-69392481f9f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_fst
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_gauss

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
theorem _root_.solution : 2 * (Fintype.card (UIdx r) : ℝ) = (r : ℝ) * (r + 1) := by
  have h := sum_fst r (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [h, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := gauss r
  push_cast
  linarith
end PI.UnitaryGroupMassFormula.LocJacTyp
