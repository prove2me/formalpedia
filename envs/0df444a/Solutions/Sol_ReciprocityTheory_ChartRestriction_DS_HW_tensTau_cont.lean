-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.tensTau_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:04.266487+00:00
-- url     : https://prove2.me/submissions/7d9741c3-f31c-4b0b-9f5c-1e486b4bade7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_continuous_tensHom

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
theorem _root_.solution (h : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ))) :
    Continuous (tensTau T ρ) :=
  continuous_tensHom h T.cont
end ReciprocityTheory.ChartRestriction.DS.HW
