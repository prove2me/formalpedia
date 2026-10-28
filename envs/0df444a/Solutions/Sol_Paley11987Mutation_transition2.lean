-- Prove2me | solution 1 for Paley11987Mutation.transition2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:26:43.7897+00:00
-- url     : https://prove2.me/submissions/cc1aeabe-3acc-4f3d-982b-a234bcc73b6f

import Definitions.Def_Paley11987MutationData
import Definitions.Def_Paley11987MutationFastData
import Theorems.Thm_Paley11987Mutation_fastTransition2

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

theorem stage2_eq : Paley11987MutationFast.stage2 = Paley11987Mutation.stage2 :=
  eq_of_chk Paley11987MutationFast.stage2Table Paley11987Mutation.stage2Values (by decide +kernel)
    (by decide +kernel)

theorem stage3_eq : Paley11987MutationFast.stage3 = Paley11987Mutation.stage3 :=
  eq_of_chk Paley11987MutationFast.stage3Table Paley11987Mutation.stage3Values (by decide +kernel)
    (by decide +kernel)

end PM213

theorem solution :
    ZP.TransitionCertificate Paley11987Mutation.stage2 Paley11987Mutation.recipe2
      Paley11987Mutation.stage3 := by
  rw [← PM213.stage2_eq, ← PM213.stage3_eq]
  exact Paley11987Mutation.fastTransition2
