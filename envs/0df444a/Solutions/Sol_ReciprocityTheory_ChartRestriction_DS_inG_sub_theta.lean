-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.inG_sub_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:27.018336+00:00
-- url     : https://prove2.me/submissions/05afad20-ae30-4167-8291-f62b2ca93ff9

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
    inG ε (M - Jm ε * Mᴴ * Jm ε) := by
  unfold inG
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_Jm,
    Jm_mul_Jm_mul, Matrix.mul_one] <;> abel
end ReciprocityTheory.ChartRestriction.DS
