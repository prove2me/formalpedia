-- Prove2me | solution 3 for SP4Mission.hurewicz
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T09:39:51.829609+00:00
-- url     : https://prove2.me/submissions/a193fd1f-3239-4794-8d34-22f85d47d47d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology
import Theorems.Thm_HurewiczSketchV2_cellular_reduction
import Theorems.Thm_HurewiczSketchV2_cellular_homology_vanish_v2
import Theorems.Thm_HurewiczSketchV2_cellular_hurewicz_isomorphism_v2

set_option autoImplicit false

open HurewiczSketchV2

theorem solution (n : ℕ) (X : Type) [TopologicalSpace X] (x : X)
    (hconn : ∀ k : ℕ, k ≤ n + 1 → Subsingleton (HomotopyGroup.Pi k X x)) :
    Nonempty (Additive (HomotopyGroup.Pi (n + 2) X x) ≃+ SP4Homology.H (n + 2) X) := by
  obtain ⟨Y, y, hY, hπ, hH⟩ := cellular_reduction n X x hconn
  have hHzero := cellular_homology_vanish_v2 n Y hY
  obtain ⟨eY⟩ := cellular_hurewicz_isomorphism_v2 n Y y hY hHzero
  obtain ⟨eπ⟩ := hπ
  obtain ⟨eH⟩ := hH
  exact ⟨eπ.symm.trans (eY.trans eH)⟩
