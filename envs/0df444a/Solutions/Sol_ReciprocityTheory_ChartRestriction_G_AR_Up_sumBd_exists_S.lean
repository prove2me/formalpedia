-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_exists_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:20.433469+00:00
-- url     : https://prove2.me/submissions/08991647-174e-49df-b970-b14be9800ee1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.PosDef) :
    ∃ S : Matrix n n ℂ, Sᴴ * H * S = 1 := by
  set U := hH.1.eigenvectorUnitary
  have hU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem U.2
  have hs : H = (U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) *
      (U : Matrix n n ℂ)ᴴ := by
    have := hH.1.spectral_theorem; rwa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at this
  let d : n → ℂ := fun i => (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
  refine ⟨(U : Matrix n n ℂ) * diagonal d, ?_⟩
  have hdH : (diagonal d)ᴴ = diagonal d := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp [d]
  rw [conjTranspose_mul, hdH, hs]
  calc diagonal d * (U : Matrix n n ℂ)ᴴ * ((U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) *
        (U : Matrix n n ℂ)ᴴ) * ((U : Matrix n n ℂ) * diagonal d)
      = diagonal d * ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) *
        ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * diagonal d := by simp only [Matrix.mul_assoc]
    _ = diagonal d * diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) * diagonal d := by
        rw [hU, Matrix.mul_one, Matrix.mul_one]
    _ = 1 := by
        rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        have hl := hH.eigenvalues_pos i
        have hsq := Real.mul_self_sqrt hl.le
        have hs0 : 0 < Real.sqrt (hH.1.eigenvalues i) := Real.sqrt_pos.mpr hl
        simp only [d, Function.comp_apply]
        rw [show ((((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) * (RCLike.ofReal (hH.1.eigenvalues i) : ℂ) *
            (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)) =
            (((Real.sqrt (hH.1.eigenvalues i))⁻¹ * hH.1.eigenvalues i * (Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
            by push_cast; rfl]
        rw [← hsq]; field_simp; simp [hs0.ne']
end ReciprocityTheory.ChartRestriction.G.AR.Up
