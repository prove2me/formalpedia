-- Prove2me | solution 1 for PermanentStars.Counting.fact_4_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:43:28.702969+00:00
-- url     : https://prove2.me/submissions/bcbe6031-c7ee-44be-a6e2-7fb08ee2d5da

import Definitions.Def_PermanentStars_Counting_Partitions

namespace PermanentStars.Counting.F42Aux
open PermanentStars.Counting

theorem assigned_iff (P : Cutoffs) (n : ℕ) (bs : Finset (Finset (Fin n))) (r : ℕ) :
    assigned P n bs = some r ↔
      (r ∈ P.R ∧ (largeCount bs r : ℚ) ≤ P.alpha r * n) ∧
      ∀ r' ∈ P.R, (largeCount bs r' : ℚ) ≤ P.alpha r' * n → r' ≤ r := by
  classical
  unfold assigned
  dsimp only
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      have hm := Finset.max'_mem _ h
      rw [Finset.mem_filter] at hm
      exact ⟨hm, fun r' hr' hc => Finset.le_max' _ r' (Finset.mem_filter.2 ⟨hr', hc⟩)⟩
    · rintro ⟨hr, hmax⟩
      apply le_antisymm
      · apply Finset.max'_le
        intro r' hr'
        rw [Finset.mem_filter] at hr'
        exact hmax r' hr'.1 hr'.2
      · exact Finset.le_max' _ r (Finset.mem_filter.2 hr)
  · simp only [reduceCtorEq, false_iff, not_and]
    intro hr _
    exact h ⟨r, Finset.mem_filter.2 hr⟩

theorem lc_ge {n : ℕ} (bs : Finset (Finset (Fin n))) (r r' : ℕ) (h : r ≤ r') :
    largeCount (bs.filter (fun B => r < B.card)) r' = largeCount bs r' := by
  unfold largeCount
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro B _
  constructor
  · exact fun h' => h'.2
  · intro h'; exact ⟨by omega, h'⟩

theorem lc_le {n : ℕ} (bs : Finset (Finset (Fin n))) (r r' : ℕ) :
    largeCount (bs.filter (fun B => r < B.card)) r' ≤ largeCount bs r' := by
  unfold largeCount
  apply Finset.card_le_card
  intro B hB
  simp only [Finset.mem_filter] at hB ⊢
  exact ⟨hB.1.1, hB.2⟩

end PermanentStars.Counting.F42Aux

open PermanentStars.Counting PermanentStars.Counting.F42Aux in
theorem solution (P : Cutoffs) (hP : P.Valid) (n : ℕ) (coverage : Covers P n)
    (S : Finset (Fin n)) (pi : Finpartition S) (r : ℕ) (hr : r ∈ P.R) :
    assigned P n pi.parts = some r ↔
      assigned P n (pi.parts.filter (fun B => r < B.card)) = some r := by
  rw [assigned_iff, assigned_iff, lc_ge _ r r le_rfl]
  constructor
  · rintro ⟨h1, hmax⟩
    refine ⟨h1, fun r' hr' hc => ?_⟩
    by_contra hlt
    push_neg at hlt
    rw [lc_ge _ r r' hlt.le] at hc
    exact absurd (hmax r' hr' hc) (by omega)
  · rintro ⟨h1, hmax⟩
    refine ⟨h1, fun r' hr' hc => ?_⟩
    by_contra hlt
    push_neg at hlt
    have : (largeCount (pi.parts.filter (fun B => r < B.card)) r' : ℚ) ≤ P.alpha r' * n := by
      rw [lc_ge _ r r' hlt.le]; exact hc
    exact absurd (hmax r' hr' this) (by omega)
