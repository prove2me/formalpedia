-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.sum_normSq_projPerp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:58.328698+00:00
-- url     : https://prove2.me/submissions/846072b7-a3bd-4f8e-9613-efab5e4432f2

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_sqNorm_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_star_dotProduct_self
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_mulVec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_star_dotProduct_projPerp_mulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex ComplexConjugate
namespace ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
private theorem sqNorm_projPerp_mulVec {g : Fin p → ℂ} (hg : g ≠ 0) (w : Fin p → ℂ) :
    sqNorm (projPerp g *ᵥ w) = sqNorm w - Complex.normSq (star g ⬝ᵥ w) / sqNorm g := by
  have key : ((sqNorm (projPerp g *ᵥ w) : ℝ) : ℂ) =
      ((sqNorm w : ℝ) : ℂ) - ((Complex.normSq (star g ⬝ᵥ w) : ℝ) : ℂ) / ((sqNorm g : ℝ) : ℂ) := by
    rw [← star_dotProduct_self (projPerp g *ᵥ w), ← star_dotProduct_self w]
    have hst : star (projPerp g *ᵥ w) =
        star w - star (((sqNorm g : ℝ) : ℂ)⁻¹ * (star g ⬝ᵥ w)) • star g := by
      rw [projPerp_mulVec, star_sub, star_smul]
    rw [hst, sub_dotProduct, smul_dotProduct, star_dotProduct_projPerp_mulVec hg, smul_zero,
      sub_zero, projPerp_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Matrix.star_dotProduct w g, Complex.star_def, mul_assoc, Complex.mul_conj]
    ring
  exact_mod_cast key
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {g : Fin p → ℂ} (hg : g ≠ 0) :
    ∑ i, ∑ l, Complex.normSq (projPerp g i l) = (p : ℝ) - 1 := by
  rw [Finset.sum_comm]
  have hcol : ∀ l, ∑ i, Complex.normSq (projPerp g i l) = 1 - Complex.normSq (g l) / sqNorm g := by
    intro l
    have h1 : sqNorm (Pi.single l (1 : ℂ)) = 1 := by
      unfold sqNorm
      rw [Finset.sum_eq_single l (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simp
    have := sqNorm_projPerp_mulVec hg (Pi.single l (1 : ℂ))
    have h2 : star g ⬝ᵥ Pi.single l (1 : ℂ) = star (g l) := by
      simp [dotProduct, Pi.single_apply]
    rw [Matrix.mulVec_single_one, h2, h1, Complex.star_def, Complex.normSq_conj] at this
    exact this
  rw [Finset.sum_congr rfl (fun l _ => hcol l), Finset.sum_sub_distrib, ← Finset.sum_div]
  change _ - sqNorm g / sqNorm g = _
  rw [div_self (sqNorm_pos hg).ne']
  simp
end ReciprocityTheory.L2DbarEstimates
