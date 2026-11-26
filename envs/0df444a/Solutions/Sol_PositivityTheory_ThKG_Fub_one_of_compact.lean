-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.one_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:03:55.906137+00:00
-- url     : https://prove2.me/submissions/9afbb45e-f1e2-4ec4-a71b-d6107d16f7f1

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
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] (f : G →* NNReal) (hf : Continuous f) {K : Set G} (hK : IsCompact K)
    {x : G} (hx : ∀ n : ℤ, x ^ n ∈ K) : f x = 1 := by
  have hbd : BddAbove (f '' K) := (hK.image hf).bddAbove
  obtain ⟨C, hC⟩ := hbd
  have hpow : ∀ n : ℤ, f x ^ n ≤ C := by
    intro n
    have := hC (Set.mem_image_of_mem f (hx n))
    rwa [map_zpow] at this
  have hne : f x ≠ 0 := by
    intro h
    have h1 : f x * f x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hle : ∀ y : NNReal, (∀ n : ℕ, y ^ n ≤ C) → y ≤ 1 := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    exact absurd (hy n) (not_le.2 hn)
  have h1 : f x ≤ 1 := hle _ fun n => by simpa using hpow n
  have h2 : (f x)⁻¹ ≤ 1 := hle _ fun n => by
    have := hpow (-(n:ℤ))
    rwa [zpow_neg, zpow_natCast, ← inv_pow] at this
  have h3 : 1 ≤ f x := by
    have := (inv_le_one₀ (pos_iff_ne_zero.2 hne)).1 h2
    exact this
  exact le_antisymm h1 h3

