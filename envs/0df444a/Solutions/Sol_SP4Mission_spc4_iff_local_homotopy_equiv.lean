-- Prove2me | solution 1 for SP4Mission.spc4_iff_local_homotopy_equiv
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-06T09:34:58.25082+00:00
-- url     : https://prove2.me/submissions/c9d1ee1e-67c6-456a-a0ed-9af821e26017

import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Definitions.Def_SP4Sphere
import Mathlib.Analysis.Normed.Module.Connected

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

/-- A local diffeomorphism from a compact connected manifold is a global
diffeomorphism if it has a continuous homotopy right inverse. -/
theorem nonempty_diffeomorph_of_local_homotopy_right_inverse
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

theorem sphere_four_connected : ConnectedSpace S4 := by
  apply Subtype.connectedSpace
  apply isConnected_sphere
  · rw [← Module.finrank_eq_rank]
    norm_num
  · norm_num

/-- For a manifold in the original conjecture, a local diffeomorphism whose
underlying continuous map is a homotopy equivalence suffices. -/
theorem diffeomorph_sphere_of_local_homotopy_equiv
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    (e : M ≃ₜ S4) (f : M ≃ₕ S4)
    (hf : IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞ f) :
    Nonempty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ S4) := by
  let : ConnectedSpace S4 := sphere_four_connected
  let : ConnectedSpace M := e.symm.surjective.connectedSpace e.symm.continuous
  exact nonempty_diffeomorph_of_local_homotopy_right_inverse f.toFun hf f.invFun f.right_inv


end SP4Mission

open SP4Mission

/-- A precise local-map reformulation, retaining the given smooth atlas. -/
theorem solution :
    SPC4 ↔
      ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M],
        Nonempty (M ≃ₜ S4) →
        ∃ f : M ≃ₕ S4, IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞ f := by
  constructor
  · intro h M _ _ _ _ _ he
    obtain ⟨d⟩ := h M he
    exact ⟨d.toHomeomorph.toHomotopyEquiv, d.isLocalDiffeomorph⟩
  · intro h M _ _ _ _ _ he
    obtain ⟨f, hf⟩ := h M he
    exact diffeomorph_sphere_of_local_homotopy_equiv M he.some f hf

#print axioms solution
