-- Prove2me | solution 1 for Paley11987Mutation.certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:27:21.289063+00:00
-- url     : https://prove2.me/submissions/3375683d-ab7e-4df4-883f-9f6f554bc64a

import Definitions.Def_Paley11987MutationData
import Definitions.Def_Paley11987MutationFastData
import Theorems.Thm_Paley11987Mutation_fastTransition0
import Theorems.Thm_Paley11987Mutation_fastTransition1
import Theorems.Thm_Paley11987Mutation_fastTransition2
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

theorem witness_eq : Paley11987MutationFast.witness = Paley11987Mutation.witness :=
  eq_of_chk Paley11987MutationFast.witnessTable Paley11987Mutation.witnessValues (by decide +kernel)
    (by decide +kernel)

theorem stage1_eq : Paley11987MutationFast.stage1 = Paley11987Mutation.stage1 :=
  eq_of_chk Paley11987MutationFast.stage1Table Paley11987Mutation.stage1Values (by decide +kernel)
    (by decide +kernel)

theorem stage2_eq : Paley11987MutationFast.stage2 = Paley11987Mutation.stage2 :=
  eq_of_chk Paley11987MutationFast.stage2Table Paley11987Mutation.stage2Values (by decide +kernel)
    (by decide +kernel)

theorem stage3_eq : Paley11987MutationFast.stage3 = Paley11987Mutation.stage3 :=
  eq_of_chk Paley11987MutationFast.stage3Table Paley11987Mutation.stage3Values (by decide +kernel)
    (by decide +kernel)

theorem stage4_eq : Paley11987MutationFast.stage4 = Paley11987Mutation.stage4 :=
  eq_of_chk Paley11987MutationFast.stage4Table Paley11987Mutation.stage4Values (by decide +kernel)
    (by decide +kernel)

open Paley11987MutationFast in
theorem closure_aux : ∀ i : Fin 2130,
    stage4Table i.val ≤ Paley11987Mutation.radius * witnessTable i.val := by
  decide +kernel

theorem closure_fast : ∀ index : Nat,
    Paley11987MutationFast.stage4 index ≤
      Paley11987Mutation.radius * Paley11987MutationFast.witness index := by
  intro i
  simp only [Paley11987MutationFast.stage4, Paley11987MutationFast.witness]
  split_ifs with h
  · exact closure_aux ⟨i, h⟩
  · simp

theorem guard0_fast : ZP.GuardCostOrder Paley11987MutationFast.witness Paley11987Mutation.recipe0 := by
  unfold ZP.GuardCostOrder
  decide +kernel

theorem guard1_fast : ZP.GuardCostOrder Paley11987MutationFast.stage1 Paley11987Mutation.recipe1 := by
  unfold ZP.GuardCostOrder
  decide +kernel

theorem guard2_fast : ZP.GuardCostOrder Paley11987MutationFast.stage2 Paley11987Mutation.recipe2 := by
  unfold ZP.GuardCostOrder
  decide +kernel

theorem guard3_fast : ZP.GuardCostOrder Paley11987MutationFast.stage3 Paley11987Mutation.recipe3 := by
  unfold ZP.GuardCostOrder
  decide +kernel

theorem aPos_fast : ∀ i j : Fin 20, i ≤ j → 1 ≤ ZP.A Paley11987MutationFast.witness i j := by
  decide +kernel

theorem bPos_fast : ∀ i j : Fin 20, i ≤ j → 1 ≤ ZP.B Paley11987MutationFast.witness i j := by
  decide +kernel

theorem output_fast : max (ZP.A Paley11987MutationFast.witness 0 0) (ZP.B Paley11987MutationFast.witness 0 0)
    = Paley11987Mutation.initialConstant := by
  decide +kernel

theorem rv0 : ZP.RecipeValid Paley11987Mutation.recipe0 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem rv1 : ZP.RecipeValid Paley11987Mutation.recipe1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem rv2 : ZP.RecipeValid Paley11987Mutation.recipe2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem rv3 : ZP.RecipeValid Paley11987Mutation.recipe3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

end PM213

open PM213 in
theorem solution : Paley11987Mutation.Certificate := by
  have g0 := guard0_fast
  have g1 := guard1_fast
  have g2 := guard2_fast
  have g3 := guard3_fast
  have s0 := Paley11987Mutation.fastTransition0
  have s1 := Paley11987Mutation.fastTransition1
  have s2 := Paley11987Mutation.fastTransition2
  have s3 := Paley11987Mutation.fastTransition3
  have cl := closure_fast
  have ap := aPos_fast
  have bp := bPos_fast
  have op := output_fast
  rw [witness_eq] at g0 s0 cl ap bp op
  rw [stage1_eq] at g1 s0 s1
  rw [stage2_eq] at g2 s1 s2
  rw [stage3_eq] at g3 s2 s3
  rw [stage4_eq] at s3 cl
  exact ⟨rv0, rv1, rv2, rv3, g0, g1, g2, g3, s0, s1, s2, s3, cl, ap, bp, op⟩
