-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.hermPart_mem_lieAlgebra_var
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:17.651708+00:00
-- url     : https://prove2.me/submissions/4bbd5799-a6ca-4c7f-abce-8f59135029d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_signMatrix_conjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_signMatrix_mul_self

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
theorem _root_.solution (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I / 2 : ℂ) • (M + Jm ε * Mᴴ * Jm ε)) := by
  have hJ := signMatrix_mul_self ε
  have hJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have key : ∀ c : ℂ, star c = -c → inG ε (c • (M + Jm ε * Mᴴ * Jm ε)) := by
    intro c hc
    unfold inG
    rw [Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, signMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose]
    rw [neg_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, neg_add_eq_zero]
    congr 1
    simp only [add_mul, mul_add, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    abel
  apply key
  rw [Complex.star_def, map_div₀, map_neg, Complex.conj_I, map_ofNat]
  ring
end ReciprocityTheory.ChartRestriction.DS
