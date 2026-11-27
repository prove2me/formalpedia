-- Prove2me | solution 2 for PositivityTheory.ThKG.Fub.one_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:27.365605+00:00
-- url     : https://prove2.me/submissions/62a6c50c-5c33-4f88-99a7-c57da6e2cd33

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
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] (f : G →* NNReal) (hf : Continuous f) {K : Set G} (hK : IsCompact K)
    {x : G} (hx : ∀ n : ℤ, x ^ n ∈ K) : f x = 1 := by
  obtain ⟨C, hC⟩ := (hK.image hf).bddAbove
  have key : ∀ y : G, (∀ n : ℕ, y ^ n ∈ K) → f y ≤ 1 := fun y hy => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact absurd (hC ⟨_, hy n, map_pow f y n⟩) (not_le.2 hn)
  have h1 := key x fun n => by simpa using hx n
  have h2 := key x⁻¹ fun n => by simpa using hx (-n)
  have h3 : f x * f x⁻¹ = 1 := by rw [← map_mul]; simp
  refine le_antisymm h1 ?_
  calc (1 : NNReal) = f x * f x⁻¹ := h3.symm
    _ ≤ f x * 1 := by gcongr
    _ = f x := mul_one _
end PositivityTheory.ThKG.Fub
