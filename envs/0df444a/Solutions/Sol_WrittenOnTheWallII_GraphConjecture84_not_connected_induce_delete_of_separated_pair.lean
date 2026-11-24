-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.not_connected_induce_delete_of_separated_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:28:32.139711+00:00
-- url     : https://prove2.me/submissions/faf2df36-250a-4436-91aa-5fc32987c1d0

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α}
    {S : Set α} {c a b : α} (hcS : c ∈ S) (haS : a ∈ S) (hbS : b ∈ S)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hac⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hbc⟩) :
    ¬ ((G.induce S).induce ({(⟨c, hcS⟩ : S)}ᶜ : Set S)).Connected := by
  let c' : S := ⟨c, hcS⟩
  let T := ({c'}ᶜ : Set S)
  let a' : T := ⟨⟨a, haS⟩, by
    change (⟨a, haS⟩ : S) ≠ c'
    intro heq
    exact hac (congrArg Subtype.val heq)⟩
  let b' : T := ⟨⟨b, hbS⟩, by
    change (⟨b, hbS⟩ : S) ≠ c'
    intro heq
    exact hbc (congrArg Subtype.val heq)⟩
  let f : (G.induce S).induce T →g G.induce ({c}ᶜ : Set α) :=
    { toFun := fun z => ⟨(z : S), by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        have hzc : (z : S) ≠ c' := by
          exact z.property
        exact hzc (Subtype.ext heq)⟩
      map_rel' := by intro u v huv; exact huv }
  intro hconn
  exact hsep ((hconn a' b').map f)
end WrittenOnTheWallII.GraphConjecture84
