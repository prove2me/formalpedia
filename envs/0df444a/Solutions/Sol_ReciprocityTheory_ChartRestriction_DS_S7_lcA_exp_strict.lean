-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lcA_exp_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:24.135368+00:00
-- url     : https://prove2.me/submissions/fd250e39-33e4-4889-afd9-65115f580cb2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ))
end ReciprocityTheory.ChartRestriction.DS.S7
