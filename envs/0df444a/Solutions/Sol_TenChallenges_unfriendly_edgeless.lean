-- Prove2me | solution 1 for TenChallenges.unfriendly_edgeless
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:23.670924+00:00
-- url     : https://prove2.me/submissions/92fa21b2-9328-4837-ab63-4d59955d0c02

import Definitions.Def_TenChallenges_Challenge_10

open scoped Cardinal

/-- With no edges, every finite partial partition is winning for every clock. -/
theorem solution {V : Type*} (f : V → Option Bool) (hf : HasFiniteDomain f)
    (α : Ordinal) : PartitionerWins (⊥ : SimpleGraph V) f α := by
  classical
  induction α using WellFoundedLT.induction generalizing f with
  | ind α ih =>
    rw [PartitionerWins]
    intro v β hβ
    let g : V → Option Bool := fun w => if w = v then some ((f v).getD false) else f w
    have hfinite : HasFiniteDomain g := by
      apply (hf.insert v).subset
      intro w hw
      by_cases hwv : w = v
      · exact Set.mem_insert_iff.mpr (Or.inl hwv)
      · exact Set.mem_insert_iff.mpr (Or.inr (by simpa [g, hwv] using hw))
    refine ⟨g, ⟨?_, hfinite, ?_⟩, ih β hβ g hfinite⟩
    · intro w b hw
      by_cases hwv : w = v
      · subst w
        simp [g, hw]
      · simp [g, hwv, hw]
    · refine ⟨(f v).getD false, by simp [g], ?_⟩
      have hempty (b : Option Bool) : IsEmpty (NeighColored (⊥ : SimpleGraph V) g v b) := by
        refine ⟨fun w => ?_⟩
        exact w.property.1
      letI := hempty (some ((f v).getD false))
      simp
