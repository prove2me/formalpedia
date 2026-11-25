-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.sum_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:05.11825+00:00
-- url     : https://prove2.me/submissions/df22a7f2-4060-42ee-a51b-2fbef3a2bab3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_uidx
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Iio__dbc53ca50bb1

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
theorem _root_.solution (r : ℕ) (f : Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, f q.1.2 = ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * f j := by
  rw [sum_uidx r (fun p => f p.2), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, card_Iio']
end PI.UnitaryGroupMassFormula.LocJacTyp
