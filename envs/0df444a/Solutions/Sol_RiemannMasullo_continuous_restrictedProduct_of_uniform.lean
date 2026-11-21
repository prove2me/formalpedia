-- Prove2me | solution 1 for RiemannMasullo.continuous_restrictedProduct_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:21:41.735264+00:00
-- url     : https://prove2.me/submissions/f98bd964-3799-48a1-b460-6029bc4c6347

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L24-L31
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

open Filter Function Set Topology RestrictedProduct
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

theorem solution {X : Type*} [TopologicalSpace X]
    {A : (i : ι) → Set (G i)} {f : X → Πʳ i, [G i, A i]}
    (hc : ∀ i, Continuous (fun x ↦ f x i)) (hA : ∀ᶠ i in cofinite, ∀ x, f x i ∈ A i) :
    Continuous f := by
  let S := {i | ∀ x, f x i ∈ A i}
  let lift (x : X) : Πʳ i, [G i, A i]_[𝓟 S] := ⟨f x, fun _ hi ↦ hi x⟩
  exact (continuous_inclusion (le_principal_iff.mpr hA)).comp
    ((continuous_rng_of_principal_iff_forall (f := lift)).mpr hc)
