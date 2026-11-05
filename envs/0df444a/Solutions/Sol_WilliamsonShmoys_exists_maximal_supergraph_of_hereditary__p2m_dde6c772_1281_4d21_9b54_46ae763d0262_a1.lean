-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_hereditary__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:16:28.171436+00:00
-- url     : https://prove2.me/submissions/31df5efa-81c1-447d-a575-c8d3f2ce7f64

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V -> Prop)
    (hmono : forall {G H : SimpleGraph V}, LE.le G H -> P H -> P G)
    (G : SimpleGraph V) (hG : P G) :
    Exists fun W : SimpleGraph V => And (LE.le G W)
      (And (P W) (forall X : SimpleGraph V, LE.le W X -> P X -> X = W)) := by
  classical
  let p : SimpleGraph V → Prop := fun W => G ≤ W ∧ P W
  have hpG : p G := ⟨le_rfl, hG⟩
  obtain ⟨W, hGW, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpW, hmax'⟩
  refine ⟨W, hpW.1, hpW.2, ?_⟩
  intro X hWX hPX
  have hpX : p X := ⟨hpW.1.trans hWX, hPX⟩
  have hXW : X ≤ W := hmax' hpX hWX
  exact le_antisymm hXW hWX
