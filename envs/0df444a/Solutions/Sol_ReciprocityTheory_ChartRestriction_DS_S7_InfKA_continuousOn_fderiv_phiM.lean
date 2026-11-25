-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.continuousOn_fderiv_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:34.442799+00:00
-- url     : https://prove2.me/submissions/03b06305-e335-4ef3-a64f-c2fe4a8032cb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_contDiffAt_phiM
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_isOpen_omega__0bdf6ae9539d

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
theorem _root_.solution (μ : Fin n → ℤ) : ContinuousOn (fderiv ℂ (PhiM μ)) (OmegaSet n) := by
  exact ContDiffOn.continuousOn_fderiv_of_isOpen
    (fun z hz => (contDiffAt_phiM μ hz).contDiffWithinAt) isOpen_omega' le_rfl
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
