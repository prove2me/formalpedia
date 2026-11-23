-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.actM_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:33.882549+00:00
-- url     : https://prove2.me/submissions/e0b1f262-76d1-4f62-a32a-ca534e5888c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA

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
open ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
namespace ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
theorem _root_.solution (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
