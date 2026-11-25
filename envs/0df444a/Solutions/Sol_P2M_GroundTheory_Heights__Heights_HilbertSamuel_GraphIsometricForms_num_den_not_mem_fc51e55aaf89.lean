-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_num_den_not_mem_fc51e55aaf89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:19.815796+00:00
-- url     : https://prove2.me/submissions/edce8e1f-73d4-4a51-91e0-9b98eca4713d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_X_inrV_5c2a2ed5768e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_rename_inlV_d9fcf2f5633e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_X_inrV_c69762fa971f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_rename_inlV_833d0140fb95


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
theorem _root_.solution {P : Ideal (MRing ι)} (hP : P.IsPrime) (g : (Σ k, ι₂ k) → MRing ι) {j : ∀ k, ι₂ k}
    (hj : ∀ k, g ⟨k, j k⟩ ∉ P) (a : K₂ → ℤ) :
    num g j a ∉ graphIdeal P g ∧ den g j a ∉ graphIdeal P g := by
  have := Ideal.Quotient.isDomain P
  have h1 : ∀ k, (C (Ideal.Quotient.mk P (g ⟨k, j k⟩)) : MvPolynomial K₂ (MRing ι ⧸ P)) ≠ 0 := by
    intro k
    rw [Ne, MvPolynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hj k
  have h2 : ∀ k, (C (Ideal.Quotient.mk P (g ⟨k, j k⟩)) * X k : MvPolynomial K₂ (MRing ι ⧸ P)) ≠ 0 :=
    fun k => mul_ne_zero (h1 k) (X_ne_zero _)
  constructor
  · rw [num, graphIdeal, RingHom.mem_ker]
    simp only [map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (pow_ne_zero _ (h1 k)) (pow_ne_zero _ (h2 k))
  · rw [den, graphIdeal, RingHom.mem_ker]
    simp only [map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (pow_ne_zero _ (h2 k)) (pow_ne_zero _ (h1 k))
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
