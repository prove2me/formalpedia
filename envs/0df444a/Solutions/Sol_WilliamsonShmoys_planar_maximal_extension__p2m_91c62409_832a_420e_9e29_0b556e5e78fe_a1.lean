-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:33:59.58262+00:00
-- url     : https://prove2.me/submissions/42aec920-76ed-4982-bb29-d9c0a35e909e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    Exists fun U : SimpleGraph V =>
      T <= U /\ WilliamsonShmoys.HasPlanarDrawingOn U /\
        forall W : SimpleGraph V, U <= W ->
          WilliamsonShmoys.HasPlanarDrawingOn W -> W = U := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G =>
    T <= G /\ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    change Exists fun G => G ∈ S
    exact Exists.intro T (Finset.mem_filter.mpr
      (And.intro (Finset.mem_univ _) (And.intro le_rfl hT)))
  have hmaxResult := S.exists_max_image (fun G => G.edgeFinset.card) hS
  let U : SimpleGraph V := hmaxResult.choose
  have hU : U ∈ S := hmaxResult.choose_spec.1
  have hmax : forall G, G ∈ S -> G.edgeFinset.card <= U.edgeFinset.card :=
    hmaxResult.choose_spec.2
  have hUmem := (Finset.mem_filter.mp hU).2
  refine Exists.intro U (And.intro hUmem.1 (And.intro hUmem.2 ?_))
  intro W hUW hW
  have hWmem : W ∈ S := Finset.mem_filter.mpr
    (And.intro (Finset.mem_univ _) (And.intro (hUmem.1.trans hUW) hW))
  have hsub : U.edgeFinset ⊆ W.edgeFinset := SimpleGraph.edgeFinset_mono hUW
  have hcard : W.edgeFinset.card <= U.edgeFinset.card := hmax W hWmem
  have heq : U.edgeFinset = W.edgeFinset := Finset.eq_of_subset_of_card_le hsub hcard
  exact SimpleGraph.edgeFinset_inj.mp heq.symm