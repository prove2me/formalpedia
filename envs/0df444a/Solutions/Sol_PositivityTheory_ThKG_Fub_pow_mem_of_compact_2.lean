-- Prove2me | solution 2 for PositivityTheory.ThKG.Fub.pow_mem_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:12.673567+00:00
-- url     : https://prove2.me/submissions/a632f575-1613-48de-b7c5-1ea0aa8e6e2d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubTate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
namespace PositivityTheory.ThKG.Fub
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G))
    {K : Set G} (hK : IsCompact K) {x : G} (hx : ∀ n : ℕ, x ^ n ∈ K) : ∃ k : ℕ, 0 < k ∧ x ^ k ∈ U := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have hf : ((QuotientGroup.mk : G → G ⧸ U) '' K).Finite := (hK.image QuotientGroup.continuous_mk).finite_of_discrete
  obtain ⟨i, j, hij, e⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ => (QuotientGroup.mk (x ^ n) : G ⧸ U))
    (fun n => Set.mem_image_of_mem _ (hx n)) hf
  refine ⟨j - i, by omega, ?_⟩
  have := QuotientGroup.eq.1 e
  rwa [show x ^ j = x ^ i * x ^ (j - i) by rw [← pow_add]; congr 1; omega, inv_mul_cancel_left] at this
end PositivityTheory.ThKG.Fub
