-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdA.continuousOn_fderiv_phiM_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:26:10.658851+00:00
-- url     : https://prove2.me/submissions/405738b1-ccaf-4d20-b05b-8e3fd2246875

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_isOpen_omega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_contDiffOn_phiM_two

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
theorem _root_.solution (μ : Fin n → ℤ) : ContinuousOn (fderiv ℂ (PhiM μ)) (OmegaSet n) :=
  (contDiffOn_phiM_two μ).continuousOn_fderiv_of_isOpen isOpen_omega (by norm_num)
end ReciprocityTheory.ChartRestriction.DS.S7.IdA
