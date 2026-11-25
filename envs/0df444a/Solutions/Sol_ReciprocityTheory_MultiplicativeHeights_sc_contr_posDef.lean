-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_contr_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:40:07.246965+00:00
-- url     : https://prove2.me/submissions/a2a81727-546b-4063-9070-9323a8a21761

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_quad_mul

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
theorem _root_.solution {r : Type*} [Fintype r] {H M : Matrix r r ℂ} (hH : H.PosDef)
    (hM : ∀ u : r → ℂ, u ≠ 0 → (star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u))).re < (star u ⬝ᵥ (H *ᵥ u)).re) :
    (H - Mᴴ * H * M).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (hH.isHermitian.sub (isHermitian_conjTranspose_mul_mul M hH.isHermitian)) ?_
  intro x hx
  rw [sub_mulVec, dotProduct_sub, sc_quad_mul]
  have h1 : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := hH.isHermitian.im_star_dotProduct_mulVec_self x
  have h2 : (star (M *ᵥ x) ⬝ᵥ (H *ᵥ (M *ᵥ x))).im = 0 :=
    hH.isHermitian.im_star_dotProduct_mulVec_self (M *ᵥ x)
  have h3 := hM x hx
  rw [Complex.lt_def, Complex.sub_re, Complex.sub_im, h1, h2, Complex.zero_re, Complex.zero_im]
  exact ⟨by linarith, by ring⟩
end ReciprocityTheory.MultiplicativeHeights
