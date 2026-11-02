-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:25:09.559309+00:00
-- url     : https://prove2.me/submissions/a68c8291-38ca-444c-bd56-2071332d6998

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    Exists (fun L : SimpleGraph V =>
      And (LE.le K L) (And (HasPlanarDrawingOn L)
        (forall M : SimpleGraph V, LE.le L M -> HasPlanarDrawingOn M -> LE.le M L))) := by
  classical
  let p : SimpleGraph V -> Prop := fun L => And (LE.le K L) (HasPlanarDrawingOn L)
  let extremalWitness := (SimpleGraph.exists_isExtremal_iff_exists p).2
    (Exists.intro K (And.intro le_rfl hK))
  let L := extremalWitness.choose
  have hNested := extremalWitness.choose_spec
  let hDec := hNested.choose
  letI : DecidableRel L.Adj := hDec
  have hExt : L.IsExtremal p := hNested.choose_spec
  apply Exists.intro L
  apply And.intro hExt.1.1
  apply And.intro hExt.1.2
  intro M hLM hM
  have hEq : L = M :=
    (SimpleGraph.IsExtremal.le_iff_eq hExt
      (And.intro (le_trans hExt.1.1 hLM) hM)).mp hLM
  exact le_of_eq hEq.symm