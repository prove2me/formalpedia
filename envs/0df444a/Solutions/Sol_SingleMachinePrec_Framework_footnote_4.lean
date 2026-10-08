-- Prove2me | solution 1 for SingleMachinePrec.Framework.footnote_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:28:35.652159+00:00
-- url     : https://prove2.me/submissions/8833dd59-780e-4eb3-9998-f62ad5c042f9

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_VertexCoverGraph

open SingleMachinePrec.Framework in
theorem solution {N : Type*} (P : N → N → Prop) [IsPartialOrder N P]
    (L : LinearExtension P) :
    (vertexCoverGraph P).IsIndepSet {u | L.Reverses u} := by
  have hT : ∀ a b c, L.le a b → L.le b c → L.le a c := fun a b c h1 h2 => by
    haveI := L.isLinearOrder; exact trans_of L.le h1 h2
  have hA : ∀ a b, L.le a b → L.le b a → a = b := fun a b h1 h2 => by
    haveI := L.isLinearOrder; exact antisymm_of L.le h1 h2
  have key : ∀ x y : IncPair P, L.Reverses x → L.Reverses y → ¬ csRule P x y := by
    intro x y hx hy h
    have hle : L.le x.1.1 x.1.2 := by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hy.1; rw [← h1, ← h2] at this; exact this
      · have := hT _ _ _ (L.extends_P _ _ h2) hy.1; rw [← h1] at this; exact this
      · exact hT _ _ _ (hT _ _ _ (L.extends_P _ _ h1) hy.1) (L.extends_P _ _ h2)
    exact hx.2 (hA _ _ hx.1 hle)
  intro u hu v hv _ hadj
  rcases hadj.2 with h | h
  · exact key u v hu hv h
  · exact key v u hv hu h
