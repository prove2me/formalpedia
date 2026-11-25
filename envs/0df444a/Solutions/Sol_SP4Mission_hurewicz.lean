-- Prove2me | solution 1 for SP4Mission.hurewicz
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-25T13:10:47.351812+00:00
-- url     : https://prove2.me/submissions/11c8402c-3e85-41dd-b5bb-10e36ca4c72c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketch
import Definitions.Def_SP4Homology
import Theorems.Thm_HurewiczSketch_cellular_reduction
import Theorems.Thm_HurewiczSketch_cellular_homology_vanish
import Theorems.Thm_HurewiczSketch_cellular_hurewicz_isomorphism

set_option autoImplicit false

open HurewiczSketch

theorem solution (n : ℕ) (X : Type) [TopologicalSpace X] (x : X)
    (hconn : ∀ k : ℕ, k ≤ n + 1 → Subsingleton (HomotopyGroup.Pi k X x)) :
    Nonempty (Additive (HomotopyGroup.Pi (n + 2) X x) ≃+ SP4Homology.H (n + 2) X) := by
  obtain ⟨Y, y, hY, hπ, hH⟩ := cellular_reduction n X x hconn
  have hHzero := cellular_homology_vanish n Y hY
  obtain ⟨eY⟩ := cellular_hurewicz_isomorphism n Y y hY hHzero
  obtain ⟨eπ⟩ := hπ
  obtain ⟨eH⟩ := hH
  exact ⟨eπ.symm.trans (eY.trans eH)⟩
