-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_quad_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:42.676242+00:00
-- url     : https://prove2.me/submissions/6c41f788-bdda-4c0e-9cac-fcf5c7801fb9

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin m → ℂ) :
    star w ⬝ᵥ ((Pᴴ * Q * P) *ᵥ w) = star (P *ᵥ w) ⬝ᵥ (Q *ᵥ (P *ᵥ w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, star_mulVec]
end ReciprocityTheory.MultiplicativeHeights
