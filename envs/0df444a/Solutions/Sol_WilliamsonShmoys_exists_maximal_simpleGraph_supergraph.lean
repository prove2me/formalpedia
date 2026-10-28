-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_simpleGraph_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:43:56.222995+00:00
-- url     : https://prove2.me/submissions/313e8950-10b6-429a-8b21-4d1aef166fe0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (Q : SimpleGraph V -> Prop) (hQ : Q G) :
    Exists fun K : SimpleGraph V => G <= K /\ Q K /\
      forall L : SimpleGraph V, K <= L -> Q L -> L = K := by
  classical
  let P : SimpleGraph V -> Prop := fun H => G <= H /\ Q H
  letI : Finite (SimpleGraph V) := inferInstance
  obtain ⟨K, hGK, hmax⟩ :=
    Finite.exists_le_maximal (p := P) (a := G) ⟨le_rfl, hQ⟩
  have hmax' := (maximal_iff_forall_gt).1 hmax
  refine ⟨K, hGK, hmax'.1.2, ?_⟩
  intro L hKL hQL
  have hPL : P L := ⟨hGK.trans hKL, hQL⟩
  have hLK : L <= K := by
    by_contra hnot
    exact hmax'.2 (lt_of_le_not_ge hKL hnot) hPL
  exact le_antisymm hLK hKL