-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.inG_add_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:23.811674+00:00
-- url     : https://prove2.me/submissions/15ea69dd-25c4-4440-a566-9e3a18f7dbc4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Jm_conjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Jm_mul_Jm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Jm_mul_Jm_mul

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
  unfold inG
  have hs : star (-Complex.I) = Complex.I := by simp
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Jm_mul_Jm, Jm_mul_Jm_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  rw [hs, neg_smul, smul_add, smul_add]
  abel
end ReciprocityTheory.ChartRestriction.DS
