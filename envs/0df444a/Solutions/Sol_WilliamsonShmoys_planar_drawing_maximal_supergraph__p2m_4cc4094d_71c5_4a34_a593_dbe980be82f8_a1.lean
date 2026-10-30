-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:15.59493+00:00
-- url     : https://prove2.me/submissions/b1adccfa-41fc-4310-8997-a104719bfb29

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_card_property__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a4

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_max_card_property__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a4 J hJ
  refine ⟨K, hJK, hK, ?_⟩
  intro L hKL hL
  have hmaxL := hmax L hKL hL
  have hinj : Function.Injective
      (fun p : {p : V × V // K.Adj p.1 p.2} =>
        (⟨p.1, hKL p.2⟩ : {p : V × V // L.Adj p.1 p.2})) := by
    intro a b hab
    have hval : a.1 = b.1 :=
      congrArg (fun z : {p : V × V // L.Adj p.1 p.2} => z.1) hab
    exact Subtype.ext hval
  have hcard_ge :
      Nat.card {p : V × V // K.Adj p.1 p.2} ≤
        Nat.card {p : V × V // L.Adj p.1 p.2} :=
    Nat.card_le_card_of_injective _ hinj
  have hcard_eq :
      Nat.card {p : V × V // L.Adj p.1 p.2} =
        Nat.card {p : V × V // K.Adj p.1 p.2} :=
    Nat.le_antisymm hmaxL.1 hcard_ge
  exact hmaxL.2 hcard_eq
