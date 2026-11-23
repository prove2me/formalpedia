-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.K_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:21.374441+00:00
-- url     : https://prove2.me/submissions/c15efc34-d3fe-40d0-b7b9-8f0af4c9b112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_jH

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
namespace ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
theorem _root_.solution {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε ∧ k * kᴴ = 1 := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨⟨?_, ?_⟩, Matrix.mem_unitaryGroup_iff.mp hu⟩
  · first
    | exact Unitary.star_mem hu
    | exact unitary.star_mem hu
  · have h := congrArg Matrix.conjTranspose hc
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, jH] at h
    exact h.symm
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
