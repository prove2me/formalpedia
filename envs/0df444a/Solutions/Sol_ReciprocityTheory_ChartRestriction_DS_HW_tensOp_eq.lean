-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.tensOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:34.413953+00:00
-- url     : https://prove2.me/submissions/676b99ec-6900-41e6-bcfa-6258abb48512

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
  (ρ : KG ε →* unitary (Matrix ι ι ℂ))
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (k : KG ε) :
    tensOp T ρ k = tensL ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) (T.op k) := rfl
end ReciprocityTheory.ChartRestriction.DS.HW
