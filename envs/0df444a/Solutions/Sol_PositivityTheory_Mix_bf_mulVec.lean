-- Prove2me | solution 1 for PositivityTheory.Mix.bf_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:51.456491+00:00
-- url     : https://prove2.me/submissions/88da31fb-3f46-4a26-b2a0-81c3a2ba9900

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) R) (u v) : bf c J (M *ᵥ u) (M *ᵥ v) = bf c (Mᵀ * J * M.map c) u v := by
  have hc : (fun i => c ((M *ᵥ v) i)) = M.map c *ᵥ fun i => c (v i) := by
    funext i
    simp [mulVec, dotProduct, map_sum, map_mul]
  simp only [bf]
  rw [hc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Mᵀ, vecMul_transpose]
end PositivityTheory.Mix
