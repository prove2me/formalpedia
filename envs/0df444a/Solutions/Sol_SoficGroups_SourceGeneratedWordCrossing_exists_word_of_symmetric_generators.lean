-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.exists_word_of_symmetric_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/10b8611b-c171-4918-9b29-4be6ddb2fcd0

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    {H : Type*} [Group H]
    (S : Finset H)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set H) = ⊤)
    (g : H) :
    ∃ l : List ↥S,
      ((l.map fun i : ↥S => (i : H)).prod) = g := by
  classical
  have hg : g ∈ Subgroup.closure (S : Set H) := by
    rw [hgenerates]
    simp
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      exact ⟨[⟨x, hx⟩], by simp⟩
  | one =>
      exact ⟨[], by simp⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨lx, hlx⟩ := ihx
      obtain ⟨ly, hly⟩ := ihy
      refine ⟨lx ++ ly, ?_⟩
      rw [List.map_append, List.prod_append, hlx, hly]
  | inv x _ ih =>
      obtain ⟨l, hl⟩ := ih
      let invLetter : ↥S → ↥S :=
        fun i => ⟨(i : H)⁻¹, hsymmetric (i : H) i.property⟩
      refine ⟨(l.map invLetter).reverse, ?_⟩
      rw [List.map_reverse, List.map_map]
      change ((l.map fun i : ↥S => (i : H)⁻¹).reverse).prod = x⁻¹
      have hmap :
          (l.map fun i : ↥S => (i : H)⁻¹) =
            (l.map (fun i : ↥S => (i : H))).map
              (fun z : H => z⁻¹) := by
        rw [List.map_map]
        rfl
      rw [hmap, ← List.prod_inv_reverse, hl]
end SoficGroups.SourceGeneratedWordCrossing
