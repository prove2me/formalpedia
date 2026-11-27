-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdA.continuousOn_second_fderiv_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:26:15.369925+00:00
-- url     : https://prove2.me/submissions/5f49e470-9557-433b-816b-aa9975d864f3

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
theorem _root_.solution (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (fderiv ℂ (PhiM μ))) (OmegaSet n) :=
  ((contDiffOn_phiM_two μ).fderiv_of_isOpen isOpen_omega (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
    isOpen_omega le_rfl
end ReciprocityTheory.ChartRestriction.DS.S7.IdA
