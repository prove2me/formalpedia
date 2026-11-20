-- Prove2me | solution 1 for VWZClique.free_words
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T01:07:48.324596+00:00
-- url     : https://prove2.me/submissions/ddf8ff93-3148-42c6-be48-1eb82a8e8008

import Definitions.Def_VWZClique_Free
open VWZClique

theorem solution {L : ℕ} (m : Mask L) (x y : PairBits L) :
    swapOK m x y ↔ ∃! pq : Free m × Free m, expand m pq = (x,y) := by
  let readFree (w : Bits L) : Free m := fun i => w i.val
  have read_fill (p : Free m) (slot : (Bool × Bool × Bool × Bool) → Bool) :
      readFree (fill m slot p) = p := by
    funext i
    simp [readFree, fill, i.property]
  have supported (pq : Free m × Free m) :
      swapOK m (expand m pq).1 (expand m pq).2 := by
    intro i
    cases h : m i with
    | none => simp [expand, fill, h]
    | some r => obtain ⟨s,u,v,t⟩ := r; simp [expand, fill, h]
  constructor
  · intro hx
    refine ⟨(readFree x.1, readFree x.2), ?_, ?_⟩
    · apply Prod.ext <;> apply Prod.ext <;> funext i <;> have hi := hx i <;>
        cases h : m i <;> simp [h] at hi <;> simp [expand, fill, readFree, h] <;> grind
    · intro b hb
      have hs := congrArg (fun p : PairBits L × PairBits L => readFree p.1.1) hb
      have hu := congrArg (fun p : PairBits L × PairBits L => readFree p.1.2) hb
      apply Prod.ext
      · simpa [expand, read_fill] using hs
      · simpa [expand, read_fill] using hu
  · rintro ⟨a, ha, _⟩
    have h := supported a
    simpa [ha] using h
