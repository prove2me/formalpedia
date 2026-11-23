-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.inG_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:14.049262+00:00
-- url     : https://prove2.me/submissions/acd02be2-610d-4165-9b3d-ae0ed0feba10

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
theorem _root_.solution (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (Complex.I • (M + Jm ε * Mᴴ * Jm ε)) := by
  unfold inG
  have hY : (M + Jm ε * Mᴴ * Jm ε)ᴴ * Jm ε = Jm ε * (M + Jm ε * Mᴴ * Jm ε) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, jH,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, jj, jj_mul, Matrix.mul_one]
    abel
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.smul_mul, hY, Matrix.mul_smul,
    neg_smul, neg_add_cancel]
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
