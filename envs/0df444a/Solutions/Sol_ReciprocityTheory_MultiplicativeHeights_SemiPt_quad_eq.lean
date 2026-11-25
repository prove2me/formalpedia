-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.quad_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:24:45.874175+00:00
-- url     : https://prove2.me/submissions/c3fea66e-7cfb-44dc-80d0-b320480a1a3a

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {r k : ℕ} (E : Matrix (Fin r) (Fin k) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin k → ℂ) : star v ⬝ᵥ ((Eᴴ * X * E) *ᵥ v) = star (E *ᵥ v) ⬝ᵥ (X *ᵥ (E *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
