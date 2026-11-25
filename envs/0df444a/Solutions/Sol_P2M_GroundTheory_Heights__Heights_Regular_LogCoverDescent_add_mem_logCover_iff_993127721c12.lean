-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_add_mem_logCover_iff_993127721c12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:48:47.079342+00:00
-- url     : https://prove2.me/submissions/24ec92fb-e3d3-4dfa-adfb-bd1baa69aa76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
namespace GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
theorem _root_.solution {v : Fin n → ℂ} (hre : ∀ k : Fin n, (v k).re = 0)
    (hz : ∀ k : Fin n, a ≤ k.val → v k = 0) (w : Fin n → ℂ) :
    w + v ∈ logCover h ↔ w ∈ logCover h := by
  simp only [logCover, Set.mem_ofPred_eq, Pi.add_apply, Complex.add_re, hre, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    simpa [hz k hk] using h2 k hk
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    simpa [hz k hk] using h2 k hk
end GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
