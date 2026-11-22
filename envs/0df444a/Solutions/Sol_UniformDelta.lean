-- Prove2me | solution 1 for UniformDelta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:15:01.653224+00:00
-- url     : https://prove2.me/submissions/bc89a024-63fb-404a-9695-211dc15f2b0b

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_UniformDelta

set_option autoImplicit false

theorem _root_.solution (X : Type) [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (F : X → ℝ)
    (hF : ContinuousOn F K) (hFnn : ∀ z ∈ K, 0 ≤ F z)
    (U : Set X) (hU : IsOpen U) (hsub : {z ∈ K | F z = 0} ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ {z ∈ K | F z ≤ δ} ⊆ U := by
  by_cases hempty : (K \ U) = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro z hz
    by_contra hzU
    exact Set.notMem_empty z (hempty ▸ (show z ∈ K \ U from ⟨hz.1, hzU⟩))
  · have hcomp : IsCompact (K \ U) := hK.diff hU
    have hne : (K \ U).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨z₀, hz₀, hmin⟩ := hcomp.exists_isMinOn hne (hF.mono Set.sdiff_subset)
    have hpos : 0 < F z₀ := by
      rcases lt_or_eq_of_le (hFnn z₀ hz₀.1) with h | h
      · exact h
      · exact absurd (hsub ⟨hz₀.1, h.symm⟩) hz₀.2
    refine ⟨F z₀ / 2, by positivity, ?_⟩
    intro z hz
    by_contra hzU
    have hle : F z₀ ≤ F z := hmin ⟨hz.1, hzU⟩
    have hz2 : F z ≤ F z₀ / 2 := hz.2
    linarith
