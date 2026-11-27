-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.qdet_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:35.720427+00:00
-- url     : https://prove2.me/submissions/e4b35252-fe75-426c-80a2-44e389a55389

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QdetMemAdjSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open PI.DSInfCharCap
open scoped InnerProductSpace Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  all_goals first
    | (funext k; simp [Formalism.REAL.Tm, apply_ite])
    | (congr 1; funext k; simp [Formalism.REAL.Tm, apply_ite])
end PI.UnitaryGroupMassFormula.DSIC
