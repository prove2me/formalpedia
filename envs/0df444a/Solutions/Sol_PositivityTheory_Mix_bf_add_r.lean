-- Prove2me | solution 1 for PositivityTheory.Mix.bf_add_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:28:13.719424+00:00
-- url     : https://prove2.me/submissions/a5ddf0a2-ba9d-4100-ab3d-458b125406c8

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Mix
open Matrix
variable {R : Type} [CommRing R] {n k : ℕ}
variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}
namespace PositivityTheory.Mix
theorem _root_.solution (u v v') : bf c J u (v + v') = bf c J u v + bf c J u v' := by
  have e : (fun i => c ((v + v') i)) = (fun i => c (v i)) + (fun i => c (v' i)) := by
    funext i
    simp
  simp only [bf, e, mulVec_add, dotProduct_add]
end PositivityTheory.Mix
