-- Prove2me | solution 1 for PI.IsoDerivBFintype.aeval_mY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:33.850953+00:00
-- url     : https://prove2.me/submissions/57fd05a1-8999-40e5-9c36-cf7bca34679e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_IsoDerivB
import Theorems.Thm_PI_IsoDerivBFintype_minor_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) (nu : Lt → YoungDiagram)
namespace PI.IsoDerivBFintype
theorem _root_.solution (J : ColChoice N nu) :
    MvPolynomial.aeval (gD s y') (mY tp nu J) =
      ∑ I : ColChoice N' nu, PIJ tp nu s I J * MvPolynomial.C (minY N' nu I (frC tp y')) := by
  unfold mY
  rw [map_prod]
  simp only [map_prod, minor_expand]
  rw [Finset.prod_congr rfl fun z _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun I => ?_
  simp only [Equiv.refl_apply, PIJ, minY, Finset.prod_mul_distrib, map_prod]
end PI.IsoDerivBFintype
