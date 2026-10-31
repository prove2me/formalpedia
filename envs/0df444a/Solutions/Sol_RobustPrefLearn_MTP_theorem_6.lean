-- Prove2me | solution 1 for RobustPrefLearn.MTP.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:52:43.434055+00:00
-- url     : https://prove2.me/submissions/33bf3aef-7e76-4c15-869d-4b0dd5165811

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp
import Theorems.Thm_RobustPrefLearn_MTP_theorem_6_finite
import Theorems.Thm_RobustPrefLearn_MTP_theorem_6_limsup

open scoped ENNReal Topology

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (C0 : ℝ) (β : ℝ → ℝ)
    (hβ : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < β δ ∧ β δ ≤ C0 + Real.log (1 / δ))
    (S1 : DS K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1, expTau (mtp p S1 (β δ)) f < ⊤) ∧
    Filter.limsup (fun δ : ℝ => expTau (mtp p S1 (β δ)) f / ENNReal.ofReal (Real.log (1 / δ)))
        (𝓝[>] 0) ≤ (IOA (K := K) p)⁻¹ :=
  ⟨fun δ _ => theorem_6_finite K hK p hp0 hp1 (β δ) S1 f hf,
    theorem_6_limsup K hK p hp0 hp1 C0 β hβ S1 f hf⟩
