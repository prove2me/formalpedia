-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.SecondJetClippedRectangle.outside_sum
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T06:04:23.11373+00:00
-- url     : https://prove2.me/submissions/4fa40c0b-6bb3-4306-805f-4dd989690f14

import Mathlib
import Definitions.Def_ProximityPrize_SubmissionLower_SecondJetClippedRectangle_corner

namespace ProximityPrize.SubmissionLower.SecondJetClippedRectangle
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem _root_.solution (A B C H : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hkA : corner A B H ≤ A) (hkB : corner A B H ≤ B) :
    (∑ i ∈ Finset.range A, ∑ j ∈ Finset.range B, if H < i+j then C-i-j else 0) =
      ∑ i ∈ Finset.range (corner A B H), ∑ j ∈ Finset.range (corner A B H),
        if i+j < corner A B H then C-(A-1-i)-(B-1-j) else 0 := (by
  classical
  let s := ((Finset.range A) ×ˢ (Finset.range B)).filter (fun p => H < p.1+p.2)
  let t := ((Finset.range (corner A B H)) ×ˢ (Finset.range (corner A B H))).filter
    (fun p => p.1+p.2 < corner A B H)
  have heq : (∑ p ∈ s, (C-p.1-p.2)) =
      ∑ p ∈ t, (C-(A-1-p.1)-(B-1-p.2)) := by
    apply Finset.sum_bij (fun p _ => (A-1-p.1,B-1-p.2))
    · intro p hp
      simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      dsimp only [corner] at hkA hkB ⊢
      omega
    · intro p hp q hq hpq
      simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp hq
      have h1 := congrArg Prod.fst hpq
      have h2 := congrArg Prod.snd hpq
      apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega
    · intro p hp
      simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      refine ⟨(A-1-p.1,B-1-p.2),?_,?_⟩
      · simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.fst, Prod.snd]
        dsimp [corner] at hp hkA hkB
        omega
      · apply Prod.ext <;> dsimp <;> omega
    · intro p hp
      have hpmem : (p.1 < A ∧ p.2 < B) ∧ H < p.1+p.2 := by
        simpa only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] using hp
      change C-p.1-p.2 = C-(A-1-(A-1-p.1))-(B-1-(B-1-p.2))
      omega
  simpa only [s,t,Finset.sum_filter,Finset.sum_product] using heq
)
end ProximityPrize.SubmissionLower.SecondJetClippedRectangle
