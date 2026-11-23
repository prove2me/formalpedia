-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.actM_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:33.829584+00:00
-- url     : https://prove2.me/submissions/ab9e137d-864b-4792-9b13-2609b45423a4

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
theorem _root_.solution (a b : Fin n) : actM E (Matrix.single a b 1) = E a b := by
  simp only [actM, Matrix.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Ne.symm hi]
  · simp
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
