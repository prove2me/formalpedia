-- Prove2me | solution 1 for ShiEmbed.layerOk_closure_append_embedCirc
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T07:33:10.620198+00:00
-- url     : https://prove2.me/submissions/ca8e8357-8136-4675-a179-41492afea26e

import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

open ShiEmbed ShiShallow

/-- The support of a relabelled instruction is the image of its support. Only the `cnot` case
is nontrivial (a two-element `Finset`). -/
private theorem shiWf_support_embedInstr {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (a : Instr m) :
    Instr.support (embedInstr e he a) = (Instr.support a).image e := by
  cases a <;>
    simp [embedInstr, Instr.support, Finset.image_insert, Finset.image_singleton]

/-- Relabelling along an injection PRESERVES layer well-formedness. This is the only direction
of `LayerOk (embedLayer e he l) ↔ LayerOk l` that the closure obligation needs; injectivity of
`e` is what makes it true, since images of disjoint sets under a non-injective map can meet. -/
private theorem shiWf_layerOk_embedLayer {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (l : List (Instr m)) (hl : LayerOk l) :
    LayerOk (embedLayer e he l) := by
  have hl' : l.Pairwise
      (fun a b => Disjoint (Instr.support a) (Instr.support b)) := hl
  show (List.map (embedInstr e he) l).Pairwise
        (fun a b => Disjoint (Instr.support a) (Instr.support b))
  rw [List.pairwise_map]
  refine hl'.imp ?_
  intro a b hab
  show Disjoint (Instr.support (embedInstr e he a)) (Instr.support (embedInstr e he b))
  rw [shiWf_support_embedInstr e he a, shiWf_support_embedInstr e he b]
  exact (Finset.disjoint_image he).mpr hab

/-- The two closure properties of layer-wise well-formedness needed by the majority
amplification construction: it survives relabelling along an injection (`embedCirc`, a
`List.map`) and concatenation of circuits (`++`). -/
theorem solution {m n : ℕ}
    (e : Fin m → Fin n) (he : Function.Injective e) :
    (∀ (c : Layered m), (∀ l ∈ c, LayerOk l) →
        ∀ l ∈ ShiEmbed.embedCirc e he c, LayerOk l)
      ∧ (∀ (c1 c2 : Layered n), (∀ l ∈ c1, LayerOk l) → (∀ l ∈ c2, LayerOk l) →
        ∀ l ∈ c1 ++ c2, LayerOk l) := by
  refine ⟨?_, ?_⟩
  · intro c hc l hl
    have hl' : l ∈ c.map (embedLayer e he) := hl
    rcases List.mem_map.mp hl' with ⟨l0, hl0, rfl⟩
    exact shiWf_layerOk_embedLayer e he l0 (hc l0 hl0)
  · intro c1 c2 h1 h2 l hl
    rcases List.mem_append.mp hl with h | h
    · exact h1 l h
    · exact h2 l h
