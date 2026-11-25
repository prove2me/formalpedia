-- Prove2me | solution 1 for PositivityTheory.Mix.bf_smul_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:51.935831+00:00
-- url     : https://prove2.me/submissions/2c391ab6-a24f-4340-8b6d-c96fdafc3f43

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
theorem _root_.solution (a : R) (u v) : bf c J u (a • v) = c a * bf c J u v := by
  have e : (fun i => c ((a • v) i)) = c a • (fun i => c (v i)) := by
    funext i
    simp
  simp only [bf, e, mulVec_smul, dotProduct_smul, smul_eq_mul]
end PositivityTheory.Mix
