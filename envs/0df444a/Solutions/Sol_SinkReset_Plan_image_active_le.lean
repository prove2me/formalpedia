-- Prove2me | solution 1 for SinkReset.Plan.image_active_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:27.339601+00:00
-- url     : https://prove2.me/submissions/d5b0e2ca-5162-49f3-bec1-5b572385df25

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_zero
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem image_active_le' {n : ℕ} [NeZero n] (S : Finset (Fin n)) (g : Fin n → Fin n) (hg : g 0 = 0) :
    ((S.image g).erase 0).card ≤ (S.erase 0).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S.erase 0) (f := g))
  intro x hx
  obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
  refine Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨fun h => hx0 (h ▸ hg), hp⟩, rfl⟩
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
end Plan
end SinkReset
end
end

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution (S : Finset (Fin n)) (w : List (Letter n))
    (hw : A.IsWord w) :
    (active (S.image (act w))).card ≤ (active S).card :=
  image_active_le' S (act w) (act_zero A w hw)
end SinkReset.Plan
