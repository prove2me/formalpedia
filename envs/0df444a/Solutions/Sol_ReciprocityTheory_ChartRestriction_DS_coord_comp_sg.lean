-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coord_comp_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:29.164233+00:00
-- url     : https://prove2.me/submissions/f5fd2a06-4ac9-4cc5-8b05-98f56861d238

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockBasis_wt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (s : Finset (Fin (n * n))) (c : Fin n) :
    (fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock c c = ((fockWt ε s c : ℝ) : ℂ) • (fockBasis n).coord s := by
  classical
  refine (fockBasis n).ext fun t => ?_
  simp only [LinearMap.comp_apply, fockBasis_wt, map_smul, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · subst h
    rfl
  · simp
end ReciprocityTheory.ChartRestriction.DS
