-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.inv_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:15.989416+00:00
-- url     : https://prove2.me/submissions/01485a10-572d-48c3-a6ee-17be6723ba3c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_jj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_jH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_jj_mul

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
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ g' ∈ UJset ε, g * g' = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  have hg' : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, jj]
  have hgg : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp hg'
  have e1 : g * (Jm ε * gᴴ * Jm ε) * Jm ε = g * Jm ε * gᴴ := by
    simp only [Matrix.mul_assoc, jj, Matrix.mul_one]
  have hgJ : g * Jm ε * gᴴ = Jm ε := by rw [← e1, hgg, Matrix.one_mul]
  refine ⟨Jm ε * gᴴ * Jm ε, ?_, hgg⟩
  show (Jm ε * gᴴ * Jm ε)ᴴ * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, jH, Matrix.conjTranspose_conjTranspose]
  have h2 : g * (Jm ε * (gᴴ * Jm ε)) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgJ, jj]
  simp only [Matrix.mul_assoc, jj_mul, h2, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
