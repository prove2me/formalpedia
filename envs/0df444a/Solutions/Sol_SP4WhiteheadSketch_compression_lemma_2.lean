-- Prove2me | solution 2 for SP4WhiteheadSketch.compression_lemma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T11:43:18.942513+00:00
-- url     : https://prove2.me/submissions/72f85b96-86d9-45ab-931d-38d4f9ecc769
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4WhiteheadSketch
import Definitions.Def_OAIQWUFI001
import Theorems.Thm_OAI_UniversalFInfinity_Cellular_contractible_of_sphereFillable
import Theorems.Thm_weaklyContractible_sphereFillable

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap

universe u v

theorem solution
    (X : Type u) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (y : Y) (hweak : SP4WeakHomotopy.WeaklyContractible Y)
    (f : C(X, Y)) (hfcell : SP4WhiteheadSketch.CellularMap f) :
    Homotopic f (ContinuousMap.const X y) := by
  letI : Nonempty Y := hweak.1
  haveI : ContractibleSpace Y :=
    OAI.UniversalFInfinity.Cellular.contractible_of_sphereFillable
      (weaklyContractible_sphereFillable Y hweak)
  obtain ⟨y0, hy0⟩ := (contractible_iff_id_nullhomotopic Y).mp inferInstance
  have hf0 : Homotopic f (ContinuousMap.const X y0) := by
    simpa using hy0.comp (Homotopic.refl f)
  haveI : Subsingleton (HomotopyGroup.Pi 0 Y y0) := hweak.2 0 y0
  let e := HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := y0)
  haveI : Subsingleton (ZerothHomotopy Y) :=
    ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩
  have hmk : ZerothHomotopy.mk y0 = ZerothHomotopy.mk y := Subsingleton.elim _ _
  have hpath : Joined y0 y := Quotient.exact hmk
  exact hf0.trans ⟨hpath.somePath.toHomotopyConst⟩
