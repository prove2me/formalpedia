-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.star_dot_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:26.087357+00:00
-- url     : https://prove2.me/submissions/cf96ccc1-23b3-4a1c-b1c9-7dc22a2b84d5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM
namespace PositivityTheory.Rg.Sw.WR.G.GM
theorem _root_.solution {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
  have h1 : star (star v ⬝ᵥ (b *ᵥ v)) = star (b *ᵥ v) ⬝ᵥ v := by
    simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : star (b *ᵥ v) = star v ᵥ* b := by rw [star_mulVec, hb.eq]
  rw [h1, h2, dotProduct_mulVec]
end PositivityTheory.Rg.Sw.WR.G.GM
