-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_det_one_add_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:54.784703+00:00
-- url     : https://prove2.me/submissions/483e8940-dc83-4627-a086-b54eb13e77d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_prod_one_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) : 1 + (trace P).re ≤ (det (1 + P)).re := by
  set U := hP.1.eigenvectorUnitary
  have hU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  have hs : P = (U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ hP.1.eigenvalues) *
      star (U : Matrix n n ℂ) := by
    have := hP.1.spectral_theorem; rwa [Unitary.conjStarAlgAut_apply] at this
  have hd : diagonal (fun i => 1 + ((hP.1.eigenvalues i : ℝ) : ℂ)) =
      1 + diagonal (RCLike.ofReal ∘ hP.1.eigenvalues) := by
    rw [← diagonal_one, diagonal_add]; rfl
  have h1 : 1 + P = (U : Matrix n n ℂ) * diagonal (fun i => 1 + ((hP.1.eigenvalues i : ℝ) : ℂ)) *
      star (U : Matrix n n ℂ) := by
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU, ← hs]
  have hdet : det (1 + P) = ∏ i, (1 + ((hP.1.eigenvalues i : ℝ) : ℂ)) := by
    rw [h1, det_mul, det_mul, det_diagonal]
    have : det (U : Matrix n n ℂ) * det (star (U : Matrix n n ℂ)) = 1 := by rw [← det_mul, hU, det_one]
    linear_combination (∏ i, (1 + ((hP.1.eigenvalues i : ℝ) : ℂ))) * this
  have htr : (trace P).re = ∑ i, hP.1.eigenvalues i := by
    rw [hP.1.trace_eq_sum_eigenvalues]; simp
  rw [hdet, htr]
  have : (∏ i, (1 + ((hP.1.eigenvalues i : ℝ) : ℂ))) = ((∏ i, (1 + hP.1.eigenvalues i) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.ofReal_re]
  exact sumBd_prod_one_add _ _ hP.eigenvalues_nonneg
end ReciprocityTheory.ChartRestriction.G.AR.Up
