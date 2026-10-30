-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:19.928572+00:00
-- url     : https://prove2.me/submissions/c3746788-4b4c-4f24-8009-527e3cbe7bed

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ (J : SimpleGraph V),
        H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨K, ?_⟩
    simp [S, hK]
  obtain ⟨H, hHS, hmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hS
  have hKH : K ≤ H := (Finset.mem_filter.mp hHS).2.1
  have hPH : WilliamsonShmoys.HasPlanarDrawingOn H :=
    (Finset.mem_filter.mp hHS).2.2
  refine ⟨H, hKH, hPH, ?_⟩
  intro J hHJ hPJ
  by_contra hJH
  have hlt : H < J := (lt_iff_le_not_ge).2 ⟨hHJ, hJH⟩
  have hss : H.edgeFinset ⊂ J.edgeFinset :=
    SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have hcard : H.edgeFinset.card < J.edgeFinset.card := Finset.card_lt_card hss
  have hJmem : J ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨le_trans hKH hHJ, hPJ⟩
  have hmaxJ := hmax J hJmem
  omega