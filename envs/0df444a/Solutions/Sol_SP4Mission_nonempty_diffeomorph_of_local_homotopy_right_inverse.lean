-- Prove2me | solution 1 for SP4Mission.nonempty_diffeomorph_of_local_homotopy_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-06T09:34:57.483305+00:00
-- url     : https://prove2.me/submissions/cf10166f-7399-4841-a350-9ece3eb2ee93

import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
open scoped Topology Manifold ContDiff
open ContinuousMap

namespace SP4Mission
/-- A connected covering with a homotopy right inverse has one sheet. -/
theorem covering_bijective_of_homotopy_right_inverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace X] [Nonempty Y]
    (f : C(X, Y)) (hf : IsCoveringMap f) (g : C(Y, X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) : Function.Bijective f := by
  classical
  obtain ⟨H⟩ := hfg
  let F := hf.liftHomotopy H.toContinuousMap g (fun y => H.apply_zero y)
  let s : C(Y, X) := F.comp ((ContinuousMap.const Y (1 : unitInterval)).prodMk
    (ContinuousMap.id Y))
  have hs : Function.RightInverse s f := by
    intro y
    exact (congr_fun (hf.liftHomotopy_lifts H.toContinuousMap g
      (fun y => H.apply_zero y)) (1, y)).trans (H.apply_one y)
  let y₀ : Y := Classical.choice inferInstance
  have hleft : s ∘ f = id := by
    apply hf.eq_of_comp_eq (s.continuous.comp f.continuous) continuous_id
      (funext fun x => hs (f x)) (s y₀)
    exact congr_arg s (hs y₀)
  exact ⟨Function.LeftInverse.injective (fun x => congr_fun hleft x), hs.surjective⟩


end SP4Mission

open SP4Mission

/-- A local diffeomorphism from a compact connected manifold is a global
diffeomorphism if it has a continuous homotopy right inverse. -/
theorem solution
    {d : ℕ}
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X]
    [PreconnectedSpace X] [Nonempty Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) Y]
    [IsManifold (𝓡 d) ∞ X] [IsManifold (𝓡 d) ∞ Y]
    (f : C(X, Y)) (hf : IsLocalDiffeomorph (𝓡 d) (𝓡 d) ∞ f)
    (g : C(Y, X)) (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) :
    Nonempty (X ≃ₘ⟮𝓡 d, 𝓡 d⟯ Y) := by
  have hcov : IsCoveringMap f := isLocalHomeomorph_iff_isCoveringMap.mp hf.isLocalHomeomorph
  exact ⟨hf.diffeomorphOfBijective
    (covering_bijective_of_homotopy_right_inverse f hcov g hfg)⟩

#print axioms solution
