-- Prove2me | solution 1 for PI.LocCartanPair.splPlane_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:20.601186+00:00
-- url     : https://prove2.me/submissions/ab243431-dd1f-46cb-beb5-5202286b58a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane

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
open PI PI.LocCartanPair
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.LocCartanPair
theorem _root_.solution {ι : Type} [Fintype ι] (A : Matrix ι ι R) (hA : Aᴴ = A) (a b : ι → R) :
    star (star a ⬝ᵥ (A *ᵥ b)) = star b ⬝ᵥ (A *ᵥ a) := by
  rw [star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec, hA]
end PI.LocCartanPair
