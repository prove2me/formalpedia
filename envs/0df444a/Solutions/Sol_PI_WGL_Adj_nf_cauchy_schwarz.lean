-- Prove2me | solution 1 for PI.WGL.Adj.nf_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:07:25.890441+00:00
-- url     : https://prove2.me/submissions/667b9985-a1af-41d3-b760-844851057f51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.Adj
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.Adj
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    ‖normFock lam y x‖ * ‖normFock lam x y‖ ≤ (normFock lam x x).re * (normFock lam y y).re := by
  letI : PreInnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nfCore lam).toCore
  exact InnerProductSpace.Core.inner_mul_inner_self_le x y
end PI.WGL.Adj
