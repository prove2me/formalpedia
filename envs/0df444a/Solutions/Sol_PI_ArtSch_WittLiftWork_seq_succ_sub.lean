-- Prove2me | solution 1 for PI.ArtSch.WittLiftWork.seq_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:22.995816+00:00
-- url     : https://prove2.me/submissions/eaa68e2d-ee66-42ff-8c6f-947ae316f438

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.WittLiftWork
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]
variable [CharP k p]
variable (hAS : ∀ a : k, ∃ y : k, y ^ p - y = a)
include hAS
namespace PI.ArtSch.WittLiftWork
theorem _root_.solution (x : WittVector p k) (n : ℕ) :
    (seq hAS x (n + 1)).1 - (seq hAS x n).1 ∈ I n := by
  obtain ⟨t, ht⟩ : ∃ t, (seq hAS x (n + 1)).1 = (seq hAS x n).1 + verschiebung^[n] t := by
    exact ⟨_, rfl⟩
  rw [ht, show ∀ u v : WittVector p k, u + v - u = v from fun u v => by abel]
  exact iterate_verschiebung_mem_I n t
end PI.ArtSch.WittLiftWork
