-- Prove2me | solution 1 for RiemannMasullo.isOpen_restrictedProduct_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:21:42.318951+00:00
-- url     : https://prove2.me/submissions/4089d864-492a-4180-85b4-5e1624948431

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L35-L47
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

open Filter Function Set Topology RestrictedProduct
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

theorem solution {A : (i : ι) → Set (G i)} (t : Set ι)
    (ht : ∀ i ∈ t, IsOpen (A i)) :
    IsOpen {x : Πʳ i, [G i, A i] | ∀ i ∈ t, x i ∈ A i} := by
  classical
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  intro S hS
  rw [le_principal_iff] at hS
  have h := (isOpen_set_pi (hS.inter_of_left t) (fun i hi ↦ ht i hi.2)).preimage
    (continuous_coe (R := G) (A := A) (𝓕 := 𝓟 S))
  convert h using 1
  ext x
  exact ⟨fun hx i hi ↦ hx i hi.2, fun hx i hi ↦
    if h : i ∈ S then x.2 h else hx i ⟨h, hi⟩⟩
