-- Prove2me | solution 1 for RiemannMasullo.restrictedProduct_topology
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:31:04.997052+00:00
-- url     : https://prove2.me/submissions/559fe67b-d1f5-4243-a9c0-516109753c1b

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L113-L144
import Theorems.Thm_RiemannMasullo_isOpen_restrictedProduct_forall_mem
import Theorems.Thm_RiemannMasullo_isCompact_closure_restrictedProduct_iff
import Definitions.Def_RiemannMasullo_RestrictedProductSplittings
import Mathlib

open Filter Function Topology
open scoped RestrictedProduct
variable {ι : Type*} (G : ι → Type*) [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
  (K : (i : ι) → Subgroup (G i)) (I₀ : Finset ι)
  (h₀ : ∀ i ∈ I₀, K i = ⊥) (h₁ : ∀ i ∉ I₀, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i)))
include h₀ h₁

open RiemannMasullo in
theorem solution :
    let P := Πʳ i, [G i, K i]
    (T2Space P ∧ LocallyCompactSpace P ∧ IsTopologicalGroup P) ∧
    (∀ K' : (i : ι) → Subgroup (G i), (∀ i ∈ I₀, K' i = ⊥) →
      (∀ i ∉ I₀, IsCompact (K' i : Set (G i)) ∧ IsOpen (K' i : Set (G i))) →
      (∀ᶠ i in cofinite, K' i = K i) →
      ∃ e : (Πʳ i, [G i, K' i]) ≃ₜ* P, ∀ x i, e x i = x i) ∧
    (∀ H : Set P, IsCompact (closure H) ↔
      ∃ B : (i : ι) → Set (G i), (∀ i, IsCompact (B i)) ∧
        (∀ᶠ i in cofinite, B i = K i) ∧ ∀ x ∈ H, ∀ i, x i ∈ B i) ∧
    (∀ J : Finset ι, ∃ e : P ≃ₜ* (((j : J) → G j) ×
      (Πʳ j : {i // i ∉ J}, [G j, K j])),
      ∀ x, (∀ j, (e x).1 j = x j) ∧ ∀ j, (e x).2 j = x j) ∧
    (∀ J : Finset ι, (∀ i ∉ J, IsOpen (K i : Set (G i))) →
      ∀ U : (i : ι) → Set (G i), (∀ i ∈ J, IsOpen (U i)) →
      IsOpen {x : P | (∀ i ∈ J, x i ∈ U i) ∧ ∀ i ∉ J, x i ∈ K i}) := by
  dsimp only
  have hK := I₀.eventually_cofinite_notMem.mono h₁
  have hOpen := hK.mono fun _ hi ↦ hi.2
  refine ⟨?_, fun K' _ _ heq ↦ ⟨restrictedProductCongr heq, fun _ _ ↦ rfl⟩,
    isCompact_closure_restrictedProduct_iff hK,
    fun J ↦ ⟨restrictedProductSplitFinset hOpen J, fun _ ↦ ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩⟩, ?_⟩
  · let e := restrictedProductSplitFinset hOpen I₀
    have : Fact (∀ j : {i // i ∉ I₀}, IsOpen (K j : Set (G j))) :=
      ⟨fun j ↦ (h₁ j j.2).2⟩
    have : LocallyCompactSpace (Πʳ j : {i // i ∉ I₀}, [G j, K j]) :=
      RestrictedProduct.locallyCompactSpace_of_group _ (.of_forall fun j ↦ (h₁ j j.2).1)
    exact ⟨inferInstance, e.toHomeomorph.isOpenEmbedding.locallyCompactSpace,
      e.toHomeomorph.isInducing.topologicalGroup e⟩
  · intro J hJ U hU
    exact ((isOpen_set_pi J.finite_toSet hU).preimage RestrictedProduct.continuous_coe).inter
      (isOpen_restrictedProduct_forall_mem (↑J : Set ι)ᶜ hJ)
