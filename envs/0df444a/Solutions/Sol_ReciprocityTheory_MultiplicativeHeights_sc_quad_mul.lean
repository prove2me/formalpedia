-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_quad_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:07.96199+00:00
-- url     : https://prove2.me/submissions/2cfe78f4-e5e7-4173-b7e3-a7948e6fd77b

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : Type*} [Fintype r] (H M : Matrix r r ℂ) (u : r → ℂ) :
    star u ⬝ᵥ ((Mᴴ * H * M) *ᵥ u) = star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u)) := by
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]
end ReciprocityTheory.MultiplicativeHeights
