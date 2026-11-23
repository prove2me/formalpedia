-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isInLieAlgebra_I_smul_add_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:18.023641+00:00
-- url     : https://prove2.me/submissions/91ece157-cc8e-4e26-9947-d18784377343

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_JJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_JH

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
theorem _root_.solution (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (Complex.I • (X + Jm ε * Xᴴ * Jm ε)) := by
  have hJJ := rq_JJ ε
  have hJH := rq_JH ε
  show (Complex.I • (X + Jm ε * Xᴴ * Jm ε))ᴴ * Jm ε + Jm ε * (Complex.I • (X + Jm ε * Xᴴ * Jm ε)) = 0
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_I, Matrix.smul_mul, Matrix.mul_smul,
    add_mul, mul_add, mul_assoc, hJJ, mul_one]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul, neg_smul, add_comm (Jm ε * X) (Xᴴ * Jm ε), neg_add_cancel]
end ReciprocityTheory.ChartRestriction.DS
