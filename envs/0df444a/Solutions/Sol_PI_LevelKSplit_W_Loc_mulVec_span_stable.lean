-- Prove2me | solution 1 for PI.LevelKSplit.W.Loc.mulVec_span_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:33.810108+00:00
-- url     : https://prove2.me/submissions/7f5ef04c-2c8a-40de-9a41-6f82cec1268e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}
namespace PI.LevelKSplit.W.Loc
theorem _root_.solution (A : Matrix (Fin n) (Fin n) B) (G : Set (Fin n → B))
    (hG : ∀ x ∈ G, A.mulVec x ∈ span O G) : ∀ x ∈ span O G, A.mulVec x ∈ span O G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx
end PI.LevelKSplit.W.Loc
