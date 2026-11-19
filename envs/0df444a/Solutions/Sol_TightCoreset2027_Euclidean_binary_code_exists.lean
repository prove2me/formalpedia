-- Prove2me | solution 1 for TightCoreset2027.Euclidean.binary_code_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:00:18.116062+00:00
-- url     : https://prove2.me/submissions/ae762c25-0806-4cb9-b459-e0252d218af7

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

private lemma word_add_self {L : ℕ} (x : Fin L → ZMod 2) : x + x = 0 := by
  ext i
  change x i + x i = 0
  have htwo : (2 : ZMod 2) = 0 := by decide
  simpa [two_mul] using congrArg (fun a : ZMod 2 => a * x i) htwo

private theorem coding_construct (L q : ℕ) (hcode : q + Nat.choose q 3 < 2 ^ L) :
    ∃ S : Finset (Fin L → ZMod 2), S.card = q ∧
      ∀ T ⊆ S, T.card = 4 → ∑ x ∈ T, x ≠ 0 := by
  classical
  induction q with
  | zero =>
    refine ⟨∅, rfl, ?_⟩
    intro T hT hc
    have : T = ∅ := Finset.subset_empty.mp hT
    simp [this] at hc
  | succ q ih =>
    have hprev : q + Nat.choose q 3 < 2 ^ L := by
      have := Nat.choose_le_choose 3 (Nat.le_succ q)
      change q + Nat.choose q 3 < 2 ^ L
      change q + 1 + Nat.choose (q + 1) 3 < 2 ^ L at hcode
      change Nat.choose q 3 ≤ Nat.choose (q + 1) 3 at this
      omega
    obtain ⟨S, hS, hgood⟩ := ih hprev
    let F := S ∪ (S.powersetCard 3).image (fun T => ∑ x ∈ T, x)
    have hF : F.card < Fintype.card (Fin L → ZMod 2) := by
      calc
        F.card ≤ S.card + ((S.powersetCard 3).image (fun T => ∑ x ∈ T, x)).card :=
          Finset.card_union_le _ _
        _ ≤ S.card + (S.powersetCard 3).card := Nat.add_le_add_left (Finset.card_image_le) _
        _ = q + Nat.choose q 3 := by simp [hS]
        _ < 2 ^ L := hprev
        _ = Fintype.card (Fin L → ZMod 2) := by simp
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := F) (t := Finset.univ) (by simpa using hF)
    have hbS : b ∉ S := by
      intro h
      exact hb (Finset.mem_union_left _ h)
    refine ⟨insert b S, by simp [hbS, hS], ?_⟩
    intro T hT hc hzero
    by_cases hbT : b ∈ T
    · let U := T.erase b
      have hUS : U ⊆ S := by
        intro x hx
        have hxT := Finset.mem_erase.mp hx
        have := hT hxT.2
        rcases Finset.mem_insert.mp this with h | h
        · exact False.elim (hxT.1 h)
        · exact h
      have hUcard : U.card = 3 := by
        dsimp [U]
        rw [Finset.card_erase_of_mem hbT, hc]
      have hsum : b + (∑ x ∈ U, x) = 0 := by
        dsimp [U]
        rw [← Finset.sum_insert (f := fun x => x) (Finset.notMem_erase b T)]
        simpa [U, Finset.insert_erase hbT] using hzero
      have heq : (∑ x ∈ U, x) = b := by
        have hh := congrArg (fun x => b + x) hsum
        simpa [← add_assoc, word_add_self] using hh
      apply hb
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨U, Finset.mem_powersetCard.mpr ⟨hUS, hUcard⟩, heq⟩
    · apply hgood T _ hc hzero
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun h => hbT (h ▸ hx))

end TightCoreset2027.Euclidean

 theorem solution (L q : ℕ) (hcode : q + Nat.choose q 3 < 2 ^ L) :
    ∃ S : Finset (Fin L → ZMod 2), S.card = q ∧
      ∀ T ⊆ S, T.card = 4 → ∑ x ∈ T, x ≠ 0 := by
  exact TightCoreset2027.Euclidean.coding_construct L q hcode
