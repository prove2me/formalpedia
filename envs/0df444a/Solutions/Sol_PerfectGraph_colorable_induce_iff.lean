-- Prove2me | solution 1 for PerfectGraph.colorable_induce_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:30:28.149571+00:00
-- url     : https://prove2.me/submissions/2766efca-01f1-47ee-93d8-7d79477304c6

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution (S : Finset V) (k : ℕ) :
    (G.induce (S : Set V)).Colorable k ↔ IsColOn G S k := by
  classical
  constructor
  · rintro ⟨f⟩
    refine ⟨fun v => if h : v ∈ S then (f ⟨v, by simpa using h⟩ : ℕ) else 0, ?_, ?_⟩
    · intro v hv
      simp [hv]
    · intro u hu v hv huv
      simp only [hu, hv, dite_true]
      intro h
      exact f.valid (v := ⟨u, by simpa using hu⟩) (w := ⟨v, by simpa using hv⟩)
        (by simpa using huv) (Fin.ext h)
  · rintro ⟨c, hc, hv⟩
    exact ⟨Coloring.mk (fun v => ⟨c v, hc v (by simp)⟩) (fun {a b} hab h =>
      hv a (by simp) b (by simp) (by simpa using hab)
        (by simpa using congrArg Fin.val h))⟩
end PerfectGraph
