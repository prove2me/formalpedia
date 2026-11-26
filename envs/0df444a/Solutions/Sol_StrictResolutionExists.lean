-- Prove2me | solution 1 for StrictResolutionExists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:31.501833+00:00
-- url     : https://prove2.me/submissions/4299feb3-7943-449f-8111-83a083ea9b6d

import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_MinimizingResolutionStrict
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_StrictResolutionExists
import Theorems.Thm_MinimizingResolutionStrict


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E)
    (hpg : IsPiecewiseGeodesic γ) (hlen : 0 < γ.len) :
    ∃ k : ℕ, 0 < k ∧ ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧ ∀ i < k, s i < s (i + 1) := by
-- BODY
  obtain ⟨k0, s0, hres0⟩ := hpg
  -- the small-edge counts at scale `δ = 1`, over all resolutions of `γ`
  have key : smallPieceCount γ 1 ∈ { c : ℕ | ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
      c = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < (1 : ℝ))).card } :=
    Nat.sInf_mem ⟨_, k0, s0, hres0, rfl⟩
  obtain ⟨k, s, hres, hcard⟩ := key
  -- a count-minimizing resolution has no degenerate edges
  have hstrict : StrictMonoOn s (Set.Icc 0 k) :=
    MinimizingResolutionStrict γ 1 one_pos k s hres hcard.symm
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      obtain ⟨-, hs0, hsk, -⟩ := hres
      rw [h, hs0] at hsk
      exact absurd hsk.symm (ne_of_gt hlen)
    · exact h
  refine ⟨k, hk, s, hres, ?_⟩
  intro i hi
  exact hstrict ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)
