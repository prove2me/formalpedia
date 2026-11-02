-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_extension__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:49:16.168303+00:00
-- url     : https://prove2.me/submissions/1526b7c5-7895-4861-aad2-1b5e5a033764

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      (∀ u v, Q.Adj u v → R.Adj u v) ∧
      HasPlanarDrawingOn R ∧
      (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
       letI : DecidableRel R.Adj := Classical.decRel R.Adj
       Q.edgeFinset.card ≤ R.edgeFinset.card) ∧
      (∀ S : SimpleGraph V, (∀ u v, R.Adj u v → S.Adj u v) →
        HasPlanarDrawingOn S →
        (letI : DecidableRel S.Adj := Classical.decRel S.Adj
         letI : DecidableRel R.Adj := Classical.decRel R.Adj
         S.edgeFinset.card ≤ R.edgeFinset.card)) := by
  classical
  let edgeBound : Nat := Fintype.card (Sym2 V)
  let candidates : Finset Nat :=
    (Finset.range (edgeBound + 1)).filter fun n =>
      ∃ G : SimpleGraph V,
        (∀ u v, Q.Adj u v → G.Adj u v) ∧
        HasPlanarDrawingOn G ∧
        G.edgeFinset.card = n
  have card_le_bound (G : SimpleGraph V) :
      G.edgeFinset.card ≤ edgeBound := by
    dsimp [edgeBound]
    exact Finset.card_le_univ _
  have hQmem : Q.edgeFinset.card ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (card_le_bound Q)), ?_⟩
    exact ⟨Q, (fun _ _ h => h), hQ, rfl⟩
  obtain ⟨n, hn, hmax⟩ :=
    Finset.exists_max_image candidates id ⟨Q.edgeFinset.card, hQmem⟩
  obtain ⟨R, hQR, hRdraw, hRcard⟩ :=
    (Finset.mem_filter.mp hn).2
  refine ⟨R, hQR, hRdraw, ?_, ?_⟩
  · calc
      Q.edgeFinset.card ≤ n := by
        exact hmax Q.edgeFinset.card hQmem
      _ = R.edgeFinset.card := hRcard.symm
  · intro S hRS hSdraw
    have hQS : ∀ u v, Q.Adj u v → S.Adj u v :=
      fun u v huv => hRS u v (hQR u v huv)
    have hSmem : S.edgeFinset.card ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (card_le_bound S)), ?_⟩
      exact ⟨S, hQS, hSdraw, rfl⟩
    calc
      S.edgeFinset.card ≤ n := hmax S.edgeFinset.card hSmem
      _ = R.edgeFinset.card := hRcard.symm