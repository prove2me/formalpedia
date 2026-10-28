-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_of_finite_subgraph_closed
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:23:41.651022+00:00
-- url     : https://prove2.me/submissions/46eb73fb-2df8-4e0b-8868-b3d337a4ebd2

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V -> Prop)
    (hdown : forall {A B : SimpleGraph V}, A <= B -> P B -> P A)
    (G : SimpleGraph V) (hG : P G) :
    Exists fun H : SimpleGraph V => G <= H /\ P H /\ forall K : SimpleGraph V, H <= K -> P K -> K = H := by
  classical
  let S : Set (SimpleGraph V) := {H | G <= H /\ P H}
  have hSfinite : S.Finite := Set.toFinite S
  have hGmem : G ∈ S := ⟨le_rfl, hG⟩
  obtain ⟨H, hGH, hHmax⟩ := hSfinite.exists_le_maximal hGmem
  refine ⟨H, hGH, hHmax.1.2, ?_⟩
  intro K hHK hPK
  have hKmem : K ∈ S := ⟨le_trans hGH hHK, hPK⟩
  have hKH : K <= H := hHmax.2 hKmem hHK
  exact le_antisymm hKH hHK