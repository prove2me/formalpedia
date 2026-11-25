-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.contDiffAt_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:25:38.197074+00:00
-- url     : https://prove2.me/submissions/d674bd16-aec7-4b5a-ad8b-864d62e5c55d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_contDiffAt_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_contDiff_lead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    ContDiffAt ℂ 1 (PhiM μ) z := by
  show ContDiffAt ℂ 1 (fun z => ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))) z
  first
  | exact contDiffAt_prod fun i _ => InfKA.contDiffAt_zpow (contDiff_lead _).contDiffAt (hz i) _
  | exact contDiffAt_finset_prod fun i _ => InfKA.contDiffAt_zpow (contDiff_lead _).contDiffAt (hz i) _
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
