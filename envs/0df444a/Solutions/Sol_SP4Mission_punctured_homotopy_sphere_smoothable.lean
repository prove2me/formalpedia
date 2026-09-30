-- Prove2me | solution 1 for SP4Mission.punctured_homotopy_sphere_smoothable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T05:10:29.754151+00:00
-- url     : https://prove2.me/submissions/c4f776ef-7497-491a-b098-8ca0598281de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Theorems.Thm_SP4Mission_quinn_compl_singleton_smoothable

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

/-!
The smoothing step of Freedman's proof of Theorem 1.6 ("apply smoothing theory for noncompact
manifolds to smooth `Σ⁴ − pt`") reduced to the general smoothing theorem for 4-manifolds
(Quinn, *Ends of maps III*, Corollary 2.2.3; Freedman–Quinn, Theorem 8.4): a connected
second-countable Hausdorff topological 4-manifold has a smooth structure in the complement of
a point. What is proved here is the topological input: a homotopy 4-sphere is connected
(path-connectedness transports along the homotopy equivalence from `S⁴`) and, being compact,
second countable.
-/

/-- Path-connectedness transports along a homotopy equivalence, from the target to the source. -/
private theorem pathConnectedSpace_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (h : ContinuousMap.HomotopyEquiv X Y) :
    PathConnectedSpace X := by
  obtain ⟨H⟩ := h.left_inv
  refine ⟨⟨h.invFun (Classical.arbitrary Y)⟩, fun x y => ?_⟩
  have p₁ : Path (h.invFun (h.toFun x)) x := H.evalAt x
  have p₂ : Path (h.invFun (h.toFun y)) y := H.evalAt y
  obtain ⟨q⟩ := PathConnectedSpace.joined (h.toFun x) (h.toFun y)
  exact ⟨p₁.symm.trans ((q.map h.invFun.continuous).trans p₂)⟩

/-- The standard four-sphere is path connected. -/
private theorem S4_pathConnectedSpace : PathConnectedSpace S4 := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  refine isPathConnected_sphere ?_ 0 zero_le_one
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M) :
    ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin 4)) {x : M // x ≠ p},
      IsManifold (𝓡 4) ∞ {x : M // x ≠ p} := by
  obtain ⟨h⟩ := hM
  -- `M` is connected: it is homotopy equivalent to the path-connected space `S⁴`.
  have : PathConnectedSpace S4 := S4_pathConnectedSpace
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv h
  -- `M` is second countable: it is compact and locally Euclidean.
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 4)) M
  -- Quinn's smoothing theorem for the complement of a point.
  exact quinn_compl_singleton_smoothable M p
