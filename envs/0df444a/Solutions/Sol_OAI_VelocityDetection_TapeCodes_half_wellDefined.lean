-- Prove2me | solution 1 for OAI.VelocityDetection.TapeCodes.half_wellDefined
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T10:26:56.1241+00:00
-- url     : https://prove2.me/submissions/09135358-9832-469a-8546-237782dc9844

import Mathlib
import Definitions.Def_NavierStokesVelocity

open OAI.VelocityDetection.TapeCodes

open scoped BigOperators Topology ContDiff

open Set Function Filter

open Set Function Filter MeasureTheory

open scoped Topology BigOperators ContDiff

open scoped Topology ContDiff BigOperators

open scoped Topology ContDiff ZeroAtInfty

open scoped Topology ContDiff ZeroAtInfty BigOperators

open scoped Topology

open OAI.VelocityDetection
open Turing Stacks

variable {b N : ℕ} [NeZero b] [NeZero N]

-- Step 2: the blank symbol (default : Fin b) has value 0.
lemma fin_blank_val : ((default : Fin b)).val = 0 := rfl

namespace P2MHole01_6048996d
theorem solution {b : ℕ} [inst : NeZero b] {bs : List ℕ} (k : ℕ) :
  Nat.ofDigits b bs = Nat.ofDigits b (bs ++ List.replicate k (0 : ℕ)) := by
  norm_num
end P2MHole01_6048996d

-- Step 4: appending zero digits does not change the base-b value.
-- riskiest
lemma ofDigits_append_zeros {bs : List ℕ} (k : ℕ) :
    Nat.ofDigits b bs = Nat.ofDigits b (bs ++ List.replicate k 0) := by
  (first | exact P2MHole01_6048996d.solution k | (apply P2MHole01_6048996d.solution <;> assumption))

theorem solution :
    ∀ a c : List (Fin b), BlankExtends a c → word a = word c := by
  intro a c h
  -- Step 1: BlankExtends a c is ∃ k, c = a ++ List.replicate k (default : Fin b).
  obtain ⟨k, rfl⟩ := h
  -- Step 3: mapping Fin.val splits over the append and turns the blank block into zeros.
  have hmap : (a ++ List.replicate k (default : Fin b)).map Fin.val =
      a.map Fin.val ++ List.replicate k 0 := by
    simp [List.map_append, fin_blank_val]
  -- Step 5: rewrite word on both sides, then the ofDigits step.
  rw [word, word, hmap]
  exact ofDigits_append_zeros k
