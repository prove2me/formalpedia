-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_property
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:31:57.120271+00:00
-- url     : https://prove2.me/submissions/192025df-e04a-49fe-a31d-acac0c540f34

import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ P L ∧
        ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by
  classical
  let Q : SimpleGraph V → Prop := fun G => K ≤ G ∧ P G
  obtain ⟨L, hLdec, hL⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 ⟨K, le_rfl, hK⟩
  letI := hLdec
  refine ⟨L, hL.1.1, hL.1.2, ?_⟩
  intro M hLM hPM
  have hQM : Q M := ⟨le_trans hL.1.1 hLM, hPM⟩
  have hEq : L = M := (hL.le_iff_eq hQM).1 hLM
  exact hEq.symm.le