-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_completion_exists_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:20:20.944513+00:00
-- url     : https://prove2.me/submissions/3792bfe9-2fbd-4e8a-b9a3-84eb8d6a6d59

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun K : SimpleGraph V =>
      And (G <= K)
        (And (WilliamsonShmoys.HasPlanarDrawingOn K)
          (forall L : SimpleGraph V,
            K <= L ->
            WilliamsonShmoys.HasPlanarDrawingOn L ->
            L <= K)) := by
  classical
  let p : SimpleGraph V -> Prop :=
    fun H => And (G <= H) (WilliamsonShmoys.HasPlanarDrawingOn H)
  have hp : p G := And.intro le_rfl hDrawing
  have hExists :
      Exists fun H : SimpleGraph V => Exists fun _ : DecidableRel H.Adj => H.IsExtremal p :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 (Exists.intro G hp)
  let K : SimpleGraph V := Classical.choose hExists
  have hKD : Exists fun _ : DecidableRel K.Adj => K.IsExtremal p :=
    Classical.choose_spec hExists
  letI : DecidableRel K.Adj := Classical.choose hKD
  have hK : K.IsExtremal p := Classical.choose_spec hKD
  refine Exists.intro K (And.intro hK.1.1 (And.intro hK.1.2 ?_))
  intro L hKL hDrawingL
  have hmax : L.edgeFinset.card <= K.edgeFinset.card :=
    hK.2 (And.intro (hK.1.1.trans hKL) hDrawingL)
  have hsubset := SimpleGraph.edgeFinset_mono hKL
  have hedge : K.edgeFinset = L.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hmax
  have hgraph : K = L := SimpleGraph.edgeFinset_inj.mp hedge
  exact le_of_eq hgraph.symm