-- Prove2me | solution 1 for SizeRamsey.Plan.star_or_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:44.004927+00:00
-- url     : https://prove2.me/submissions/dbf22c68-ae5a-450f-99a9-0bce30dd3a04

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
section
@[expose] public section
namespace SizeRamsey
end SizeRamsey
namespace SizeRamsey.Plan
private theorem edges_meet {V : Type*} {G : SimpleGraph V}
    (hmatch : ¬ HasMatching2 G) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  apply hmatch
  refine ⟨![a, b, c, d], ?_, by simpa using hab, by simpa using hcd⟩
  have hab' := hab.ne
  have hcd' := hcd.ne
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
end SizeRamsey.Plan
namespace SizeRamsey
namespace Proof
end Proof
end SizeRamsey
end
end

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*} (G : SimpleGraph V)
    (htri : ∀ a b c,
      G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hmatch : ¬ HasMatching2 G) :
    G = ⊥ ∨
      ∃ v, ∀ a b, G.Adj a b → a = v ∨ b = v := by
  by_cases hbot : G = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, y, hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.1 hbot
  by_contra hno
  push Not at hno
  obtain ⟨a, b, hab, hax, hbx⟩ := hno x
  obtain ⟨c, d, hcd, hcy, hdy⟩ := hno y
  -- an edge `y z` with `z ≠ x`
  have hz : ∃ z, G.Adj y z ∧ z ≠ x := by
    rcases edges_meet hmatch hxy hab with h | h | h | h
    · exact absurd h.symm hax
    · exact absurd h.symm hbx
    · subst h; exact ⟨b, hab, hbx⟩
    · subst h; exact ⟨a, hab.symm, hax⟩
  have hw : ∃ w, G.Adj x w ∧ w ≠ y := by
    rcases edges_meet hmatch hxy hcd with h | h | h | h
    · subst h; exact ⟨d, hcd, hdy⟩
    · subst h; exact ⟨c, hcd.symm, hcy⟩
    · exact absurd h.symm hcy
    · exact absurd h.symm hdy
  obtain ⟨z, hyz, hzx⟩ := hz
  obtain ⟨w, hxw, hwy⟩ := hw
  rcases edges_meet hmatch hyz hxw with h | h | h | h
  · exact hxy.ne h.symm
  · exact hwy h.symm
  · exact hzx h
  · subst h; exact htri x y z hxy hyz hxw.symm
end SizeRamsey.Plan
