-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.sum_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:59.442246+00:00
-- url     : https://prove2.me/submissions/aa2cddda-2b22-4422-b42c-8107cd9bc03f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_uidx
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Ioi__ab9c340c690c

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
    ∑ q : UIdx r, f q.1.1 = ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * f i := by
  rw [sum_uidx r (fun p => f p.1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, card_Ioi']
end PI.UnitaryGroupMassFormula.LocJacTyp
