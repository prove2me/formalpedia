-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_exists__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:05:32.501047+00:00
-- url     : https://prove2.me/submissions/24f33e37-8607-42ea-bf80-6e12fba8f28f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      (forall {u v : V}, L.Adj u v -> M.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (forall N : SimpleGraph V,
        (forall {u v : V}, M.Adj u v -> N.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L <= G /\ WilliamsonShmoys.HasPlanarDrawingOn G
  have hLmem : L ∈ admissible := by
    change L ∈ (Finset.univ.filter fun G => L <= G /\ WilliamsonShmoys.HasPlanarDrawingOn G)
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_univ L) (And.intro le_rfl hL))
  have hex : Exists fun G : SimpleGraph V => G ∈ admissible :=
    Exists.intro L hLmem
  have hmaxexists :=
    Finset.exists_max_image admissible (fun G => G.edgeFinset.card) hex
  let M : SimpleGraph V := Classical.choose hmaxexists
  have hMspec := Classical.choose_spec hmaxexists
  have hMmem : M ∈ admissible := hMspec.1
  have hMmax : forall G : SimpleGraph V, G ∈ admissible ->
      G.edgeFinset.card <= M.edgeFinset.card := hMspec.2
  have hMadmissible : L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M :=
    (Finset.mem_filter.mp hMmem).2
  refine Exists.intro M
    (And.intro (fun {u v : V} (huv : L.Adj u v) => hMadmissible.1 huv)
      (And.intro hMadmissible.2 ?_))
  intro N hMN hNplanar
  have hMNle : M <= N := by
    intro u v huv
    exact hMN huv
  have hLN : L <= N := by
    intro u v huv
    exact hMN (hMadmissible.1 huv)
  have hNmem : N ∈ admissible := by
    change N ∈ (Finset.univ.filter fun G => L <= G /\ WilliamsonShmoys.HasPlanarDrawingOn G)
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_univ N) (And.intro hLN hNplanar))
  by_contra hNM
  have hne : M ≠ N := by
    intro hEq
    exact hNM hEq.symm
  have hlt : M < N := lt_of_le_of_ne hMNle hne
  have hss := SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have hcard := Finset.card_lt_card hss
  have hmax := hMmax N hNmem
  omega