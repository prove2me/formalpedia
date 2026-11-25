-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.preOp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:29.591682+00:00
-- url     : https://prove2.me/submissions/d161a2c4-4731-4378-8ef5-ecf081888807

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelGenA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution : preOp τ (1 : KG ε) = 1 := by
  show ((τ 1 : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = _
  rw [map_one]; rfl
end ReciprocityTheory.ChartRestriction.DS.HW
