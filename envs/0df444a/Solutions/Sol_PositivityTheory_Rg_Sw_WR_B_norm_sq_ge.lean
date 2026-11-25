-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.norm_sq_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:32.526157+00:00
-- url     : https://prove2.me/submissions/567ea67a-089c-48f5-ab07-33f0b955aeaf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_herm_conjTranspose
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_star_dot_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y) (x : Fin n → ℂ) :
    ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖(M *ᵥ x) i‖ ^ 2 := by
  have key : ((∑ i, ‖(M *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) =
      ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) + ((∑ i, ‖(herm y *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← star_dot_self (M *ᵥ x), ← star_dot_self x, ← star_dot_self (herm y *ᵥ x)]
    simp only [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hM, herm_conjTranspose, add_mulVec, one_mulVec,
      dotProduct_add]
  have key' : ∑ i, ‖(M *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 + ∑ i, ‖(herm y *ᵥ x) i‖ ^ 2 := by
    exact_mod_cast key
  rw [key']
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => by positivity)
end PositivityTheory.Rg.Sw.WR.B
