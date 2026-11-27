-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gram_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:56:23.070869+00:00
-- url     : https://prove2.me/submissions/61d345ce-1f25-4b5b-83a4-f93905ec9108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_sum_support_eq
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_gram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (G : MvPolynomial κ K) (hG : G ≠ 0)
    (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (G * MvPolynomial.monomial m 1).support ⊆ T) (σ : K →+* ℂ) :
    2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ G) ≤
      Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ (bG G S e)).det.re := by
  have hσG : MvPolynomial.map σ G ≠ 0 := by
    intro h0; apply hG
    exact MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero])
  have hgram := ReciprocityTheory.MultiplicativeHeights.Closed.gram κ (MvPolynomial.map σ G) S hσG
  have hmap : ∀ m : κ →₀ ℕ, MvPolynomial.map σ G * MvPolynomial.monomial m 1 =
      MvPolynomial.map σ (G * MvPolynomial.monomial m 1) := by
    intro m
    rw [map_mul, MvPolynomial.map_monomial, σ.map_one]
  have heq : (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ (bG G S e)).det =
      (Matrix.of fun m m' : S => ReciprocityTheory.MultiplicativeHeights.polyInner
        (MvPolynomial.map σ G * MvPolynomial.monomial (m : κ →₀ ℕ) 1)
        (MvPolynomial.map σ G * MvPolynomial.monomial (m' : κ →₀ ℕ) 1)).det := by
    rw [← Matrix.det_submatrix_equiv_self S.equivFin.symm, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, ReciprocityTheory.MultiplicativeHeights.gramC,
      Matrix.one_mulVec, ReciprocityTheory.MultiplicativeHeights.polyInner]
    rw [sum_support_eq e]
    · simp only [dotProduct, hmap, MvPolynomial.coeff_map, ReciprocityTheory.MultiplicativeHeights.embVec, bG, coordVec, mS,
        Pi.star_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [mul_comm]
    · rw [hmap]
      exact (MvPolynomial.support_map_subset _ _).trans (hST _ (S.equivFin.symm i).2)
  have h1 := Real.log_le_log (Real.exp_pos _) hgram
  rw [Real.log_exp, ← heq] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
