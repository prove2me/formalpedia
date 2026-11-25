-- Prove2me | solution 1 for PI.LocCartanPair.splPlane_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:21.872278+00:00
-- url     : https://prove2.me/submissions/f4aa23c7-f6b4-4c72-bf80-8be179f62859

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
theorem _root_.solution {ι m n : Type} [Fintype ι] (A : Matrix ι ι R) (M : Matrix ι m R)
    (N : Matrix ι n R) (r : m) (s : n) :
    (Mᴴ * A * N) r s = star (fun i => M i r) ⬝ᵥ (A *ᵥ fun i => N i s) := by
  rw [Matrix.mul_assoc]; rfl
end PI.LocCartanPair
