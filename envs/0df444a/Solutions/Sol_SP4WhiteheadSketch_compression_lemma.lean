-- Prove2me | solution 1 for SP4WhiteheadSketch.compression_lemma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T11:01:39.850387+00:00
-- url     : https://prove2.me/submissions/2baf5bdc-5f29-438a-ab85-f11d1a4330e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Compression
import Definitions.Def_SP4WhiteheadSketch
import Theorems.Thm_SP4Compression_cellular_induction

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap
open SP4Compression

universe u v

/-- Compression lemma via cell compression and CW cellular induction.

Weak contractibility of `Y` gives `Subsingleton (π_n Y y)` for every `n`; since `π_n` is the
quotient of based generalized `n`-loops by rel-boundary homotopy, equality of classes is
exactness, so every generalized loop is homotopic to the constant rel boundary — this is
`CellCompressible Y y`, proved here without any further input.  Cellular induction then
promotes this cell-by-cell compression to a global homotopy `f ≃ const y`. -/
theorem solution
    (X : Type u) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (y : Y) (hweak : SP4WeakHomotopy.WeaklyContractible Y)
    (f : C(X, Y)) (hfcell : SP4WhiteheadSketch.CellularMap f) :
    Homotopic f (ContinuousMap.const X y) := by
  have hcell : CellCompressible Y y := by
    intro n g
    have hEq : (Quotient.mk' g : HomotopyGroup.Pi n Y y) =
        Quotient.mk' (GenLoop.const : GenLoop (Fin n) Y y) :=
      @Subsingleton.elim (HomotopyGroup.Pi n Y y) (hweak.2 n y) _ _
    exact ⟨Quotient.exact hEq⟩
  exact cellular_induction X Y y hcell f
