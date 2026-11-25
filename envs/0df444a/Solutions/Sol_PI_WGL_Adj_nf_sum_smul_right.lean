-- Prove2me | solution 1 for PI.WGL.Adj.nf_sum_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:30.081666+00:00
-- url     : https://prove2.me/submissions/f10d3320-2e65-45e6-b20b-638151800061

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Theorems.Thm_PI_WGL_Adj_nf_sum_smul_left

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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (∑ k ∈ S, a k • v k) = ∑ k ∈ S, star (a k) * normFock lam f (v k) := by
  rw [nf_herm, nf_sum_smul_left, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', ← nf_herm]
end PI.WGL.Adj
