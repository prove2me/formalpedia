-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_actM_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:25.574144+00:00
-- url     : https://prove2.me/submissions/f2434d55-da78-47cf-b4ea-c4f2cece5aaf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actM E (X + Y) = actM E X + actM E Y := by
  simp only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.DS
