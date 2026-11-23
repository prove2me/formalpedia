-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.matrixAction_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:55.545598+00:00
-- url     : https://prove2.me/submissions/85f23528-9e05-41eb-a94b-90828e5cc9dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA

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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) : actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  simp only [actM, Matrix.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero (fun y _ => if_neg (fun h => hx h.1.symm)))
    (by simp)]
  rw [Finset.sum_eq_single b (fun y _ hy => if_neg (fun h => hy h.2.symm)) (by simp)]
  simp
end ReciprocityTheory.ChartRestriction.DS
