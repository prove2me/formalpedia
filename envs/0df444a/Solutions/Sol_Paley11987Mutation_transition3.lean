-- Prove2me | solution 1 for Paley11987Mutation.transition3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:26:54.413305+00:00
-- url     : https://prove2.me/submissions/d4c666e2-02b5-4861-a68f-82f8aa0e0d6e

import Definitions.Def_Paley11987MutationData
import Definitions.Def_Paley11987MutationFastData
import Theorems.Thm_Paley11987Mutation_fastTransition3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PM213


def chk (f : Nat → Nat) : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, k => f k == x && chk f xs (k + 1)

theorem chk_spec (f : Nat → Nat) : ∀ (l : List Nat) (k : Nat), chk f l k = true →
    ∀ i, i < l.length → f (k + i) = (l[i]?).getD 0
  | [], _, _, i, hi => by simp at hi
  | x :: xs, k, h, i, hi => by
    simp only [chk, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := chk_spec f xs (k + 1) h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem eq_of_chk (f : Nat → Nat) (a : Array Nat) (hs : a.size = 2130)
    (hc : chk f a.toList 0 = true) :
    (fun index => if index < 2130 then f index else 0) =
      Paley11987Mutation.profileFromArray a := by
  funext i
  simp only [Paley11987Mutation.profileFromArray]
  split_ifs with h
  · have := chk_spec f a.toList 0 hc i (by simpa [hs] using h)
    simpa [Array.getElem?_toList] using this
  · rfl

theorem stage3_eq : Paley11987MutationFast.stage3 = Paley11987Mutation.stage3 :=
  eq_of_chk Paley11987MutationFast.stage3Table Paley11987Mutation.stage3Values (by decide +kernel)
    (by decide +kernel)

theorem stage4_eq : Paley11987MutationFast.stage4 = Paley11987Mutation.stage4 :=
  eq_of_chk Paley11987MutationFast.stage4Table Paley11987Mutation.stage4Values (by decide +kernel)
    (by decide +kernel)

end PM213

theorem solution :
    ZP.TransitionCertificate Paley11987Mutation.stage3 Paley11987Mutation.recipe3
      Paley11987Mutation.stage4 := by
  rw [← PM213.stage3_eq, ← PM213.stage4_eq]
  exact Paley11987Mutation.fastTransition3
