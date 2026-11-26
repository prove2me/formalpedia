-- Prove2me | solution 2 for SP4Mission.hurewicz
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T07:08:05.557802+00:00
-- url     : https://prove2.me/submissions/805993a3-0acf-4513-afcb-5cbc45a0949b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology
import Theorems.Thm_HurewiczSketchV2_cellular_reduction
import Theorems.Thm_HurewiczSketchV2_cellular_homology_vanish
import Theorems.Thm_HurewiczSketchV2_cellular_hurewicz_isomorphism

set_option autoImplicit false

open HurewiczSketchV2

theorem solution (n : ℕ) (X : Type) [TopologicalSpace X] (x : X)
    (hconn : ∀ k : ℕ, k ≤ n + 1 → Subsingleton (HomotopyGroup.Pi k X x)) :
    Nonempty (Additive (HomotopyGroup.Pi (n + 2) X x) ≃+ SP4Homology.H (n + 2) X) := by
  obtain ⟨Y, y, hY, hπ, hH⟩ := cellular_reduction n X x hconn
  have hHzero := cellular_homology_vanish n Y hY
  obtain ⟨eY⟩ := cellular_hurewicz_isomorphism n Y y hY hHzero
  obtain ⟨eπ⟩ := hπ
  obtain ⟨eH⟩ := hH
  exact ⟨eπ.symm.trans (eY.trans eH)⟩
