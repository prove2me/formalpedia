-- Prove2me | solution 1 for SP4Compression.cellular_induction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T12:17:18.835992+00:00
-- url     : https://prove2.me/submissions/5c5d9a03-b8bb-4bd3-abfb-9aa70b2d9f79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Definitions.Def_SP4Compression
import Theorems.Thm_SP4Compression_exists_homotopicRel_range_subset

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap Set Topology Topology.RelCWComplex

universe u v

/-- Reduce the compression lemma's cellular-induction step to the transplanted TauCeti
compression lemma.  An absolute CW complex `X` is the relative CW pair `(univ, ∅)`, and the
base condition `MapsTo f ∅ {y}` is vacuous.  The transplanted lemma supplies a map into
`{y}` homotopic to `f` after transporting along `Homeomorph.Set.univ`; a map with range in
`{y}` is the constant map. -/
theorem solution
    (X : Type u) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (Y : Type v) [TopologicalSpace Y] (y : Y)
    (hcell : SP4Compression.CellCompressible Y y)
    (f : C(X, Y)) :
    Homotopic f (ContinuousMap.const X y) := by
  let e : (Set.univ : Set X) ≃ₜ X := Homeomorph.Set.univ X
  let ec : C((Set.univ : Set X), X) := ⟨e, e.continuous⟩
  let eci : C(X, (Set.univ : Set X)) := ⟨e.symm, e.symm.continuous⟩
  let f' : C((Set.univ : Set X), Y) := f.comp ec
  have hf' : MapsTo f' {x : (Set.univ : Set X) | (x : X) ∈ (∅ : Set X)} {y} := by
    intro x hx
    exact False.elim hx
  obtain ⟨g', hfg', hgr'⟩ :=
    SP4Compression.exists_homotopicRel_range_subset X (Set.univ : Set X) (∅ : Set X)
      Y y hcell f' hf'
  have hfgHom' : Homotopic (f.comp ec) g' := by
    simpa [f'] using hfg'.homotopic
  have hgconst' : g' = ContinuousMap.const (Set.univ : Set X) y := by
    ext x
    exact hgr' ⟨x, rfl⟩
  have hleft : (f.comp ec).comp eci = f := by
    ext x
    change f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]
  have hfgHom : Homotopic f (g'.comp eci) := by
    have h := hfgHom'.map (fun H => H.compContinuousMap eci)
    rwa [hleft] at h
  have hgconst : g'.comp eci = ContinuousMap.const X y := by
    rw [hgconst']
    ext x
    rfl
  simpa [hgconst] using hfgHom
