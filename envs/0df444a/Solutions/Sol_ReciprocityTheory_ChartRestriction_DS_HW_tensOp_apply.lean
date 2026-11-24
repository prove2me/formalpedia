-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.tensOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:17.656984+00:00
-- url     : https://prove2.me/submissions/0b88d399-f1de-4ff8-a4ad-79a2acacfd4c

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
theorem _root_.solution (k : KG ε) (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensOp T ρ k x i = ∑ j, ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j • T.op k (x j) :=
  tensL_apply _ _ _ _
end ReciprocityTheory.ChartRestriction.DS.HW
