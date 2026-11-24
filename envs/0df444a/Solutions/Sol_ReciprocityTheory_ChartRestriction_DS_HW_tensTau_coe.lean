-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.tensTau_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:34:16.920474+00:00
-- url     : https://prove2.me/submissions/2cbbe240-cee5-47f4-84d1-a27dbad4e9a2

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
    ((tensTau T ρ k : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V))) :
      PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) = tensOp T ρ k := rfl
end ReciprocityTheory.ChartRestriction.DS.HW
