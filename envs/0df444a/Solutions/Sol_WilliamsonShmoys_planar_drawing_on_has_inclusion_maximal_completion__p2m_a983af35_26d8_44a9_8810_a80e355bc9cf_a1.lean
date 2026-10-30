-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_has_inclusion_maximal_completion__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:55.530299+00:00
-- url     : https://prove2.me/submissions/f498ed44-de84-4817-b685-694006bdecf7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) :
    Exists fun U : SimpleGraph V =>
      T ≤ U ∧ HasPlanarDrawingOn U ∧
        ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W ≤ U := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun U => T ≤ U ∧ HasPlanarDrawingOn U
  have hTmem : T ∈ candidates := by
    simp [candidates, hT]
  obtain ⟨U, hUmem, hmax⟩ :=
    Finset.exists_max_image candidates
      (fun G : SimpleGraph V => G.edgeFinset.card) ⟨T, hTmem⟩
  have hUprops : T ≤ U ∧ HasPlanarDrawingOn U := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hUmem
  refine ⟨U, hUprops.1, hUprops.2, ?_⟩
  intro W hUW hWdraw
  have hWmem : W ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hUprops.1.trans hUW, hWdraw⟩
  have hcard : W.edgeFinset.card ≤ U.edgeFinset.card := hmax W hWmem
  have hsubset : U.edgeFinset ⊆ W.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hUW
  have hedge : U.edgeFinset = W.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  have hEq : U = W := SimpleGraph.edgeFinset_inj.mp hedge
  rw [hEq]