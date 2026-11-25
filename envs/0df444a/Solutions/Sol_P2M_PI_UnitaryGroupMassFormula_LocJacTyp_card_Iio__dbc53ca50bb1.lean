-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Iio__dbc53ca50bb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:52.502172+00:00
-- url     : https://prove2.me/submissions/4dfb5806-75fe-4f7a-ae50-07e08fd40d7e

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
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (r : ℕ) (j : Fin (r + 1)) :
    ((Finset.univ.filter fun i : Fin (r + 1) => i < j).card : ℝ) = ((j : ℕ) : ℝ) := by
  have h : (Finset.univ.filter fun i : Fin (r + 1) => i < j) = Finset.Iio j := by ext i; simp
  rw [h, Fin.card_Iio]
end PI.UnitaryGroupMassFormula.LocJacTyp
