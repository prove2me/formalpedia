-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.gramX_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:03.34782+00:00
-- url     : https://prove2.me/submissions/d0a571dd-7e9d-4b93-8d0e-63a739842d14

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_gramX_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x)ᴴ = gramX ε x := by
  ext i j
  simp only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : star (sgn ε a) = sgn ε a := by unfold sgn; split_ifs <;> simp
  rw [this]; ring
end PositivityTheory.Rg.Sw.WR.G
