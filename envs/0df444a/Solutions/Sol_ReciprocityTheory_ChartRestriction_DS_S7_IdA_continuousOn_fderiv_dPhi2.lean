-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdA.continuousOn_fderiv_dPhi2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:43.120897+00:00
-- url     : https://prove2.me/submissions/a17b1e92-465d-4a04-8b46-f0ce5e81a5d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_isOpen_omega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_contDiffAt_dPhi2

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
open ReciprocityTheory.ChartRestriction.DS.S7.IdA
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdA
theorem _root_.solution (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (dPhi2 μ)) (OmegaSet n ×ˢ Set.univ) :=
  ContDiffOn.continuousOn_fderiv_of_isOpen (fun p hp => (contDiffAt_dPhi2 μ hp.1).contDiffWithinAt)
    (isOpen_omega.prod isOpen_univ) le_rfl
end ReciprocityTheory.ChartRestriction.DS.S7.IdA
