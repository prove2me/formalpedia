-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_exists_mul_mem_of_mem_123d02d0699d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:24.830411+00:00
-- url     : https://prove2.me/submissions/1462dec9-149d-4b73-b1d7-4f6c316b8016

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRankAdjoinFrac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Module IntermediateField IntermediateField.algebraAdjoinAdjoin
open GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
namespace GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
theorem _root_.solution {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) {y : Ω}
    (hy : y ∈ Algebra.adjoin (IntermediateField.adjoin F S) T) :
    ∃ a ∈ Algebra.adjoin F S, a ≠ 0 ∧ a * y ∈ Algebra.adjoin F T := by
  have hST := Algebra.adjoin_mono (R := F) h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_mem _, one_ne_zero, by rw [one_mul]; exact Algebra.subset_adjoin hx⟩
  | algebraMap k =>
    obtain ⟨r, hr, s, hs, hk⟩ := mem_adjoin_iff_div.mp k.2
    by_cases hs0 : s = 0
    · refine ⟨1, one_mem _, one_ne_zero, ?_⟩
      have : (algebraMap (IntermediateField.adjoin F S) Ω k) = 0 := by
        change (k : Ω) = 0
        rw [hk, hs0, div_zero]
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨s, hs, hs0, ?_⟩
      change s * (k : Ω) ∈ _
      rw [hk, mul_div_cancel₀ _ hs0]
      exact hST hr
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x + y) = b * (a * x) + a * (b * y) := by ring
    rw [this]
    exact add_mem (mul_mem (hST hb) hax) (mul_mem (hST ha) hby)
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x * y) = (a * x) * (b * y) := by ring
    rw [this]
    exact mul_mem hax hby
end GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
