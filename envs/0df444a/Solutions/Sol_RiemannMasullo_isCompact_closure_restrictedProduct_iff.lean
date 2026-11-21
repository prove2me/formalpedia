-- Prove2me | solution 1 for RiemannMasullo.isCompact_closure_restrictedProduct_iff
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:24:45.273886+00:00
-- url     : https://prove2.me/submissions/35ecdf4c-4940-42b9-8108-17d8c1962766

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L88-L124
import Theorems.Thm_RiemannMasullo_continuous_restrictedProduct_of_uniform
import Theorems.Thm_RiemannMasullo_isOpen_restrictedProduct_forall_mem
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

open Filter Function Set Topology RestrictedProduct
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

open RiemannMasullo
theorem solution {A : (i : ι) → Set (G i)} [∀ i, T2Space (G i)]
    (hA : ∀ᶠ i in cofinite, IsCompact (A i) ∧ IsOpen (A i)) (H : Set (Πʳ i, [G i, A i])) :
    IsCompact (closure H) ↔ ∃ B : (i : ι) → Set (G i), (∀ i, IsCompact (B i)) ∧
      (∀ᶠ i in cofinite, B i = A i) ∧ ∀ x ∈ H, ∀ i, x i ∈ B i := by
  classical
  constructor
  · intro hc
    let U (J : Finset ι) := {x : Πʳ i, [G i, A i] | ∀ i ∈ {i | i ∉ J ∧ IsOpen (A i)}, x i ∈ A i}
    have hmono : Monotone U := fun _ _ h _ hx i hi ↦ hx i ⟨fun hj ↦ hi.1 (h hj), hi.2⟩
    obtain ⟨J, hJ⟩ := hc.elim_directed_cover U
      (fun _ ↦ isOpen_restrictedProduct_forall_mem _ (fun _ hi ↦ hi.2))
      (fun x _ ↦ mem_iUnion.mpr ⟨(eventually_cofinite.mp x.2).toFinset,
        fun i hi ↦ by
          by_contra h
          exact hi.1 ((eventually_cofinite.mp x.2).mem_toFinset.mpr h)⟩) hmono.directed_le
    let B (i : ι) := if i ∉ J ∧ IsCompact (A i) ∧ IsOpen (A i) then A i
      else (fun x : Πʳ i, [G i, A i] ↦ x i) '' closure H
    refine ⟨B, fun i ↦ ?_, ?_, fun x hx i ↦ ?_⟩
    · dsimp only [B]
      split_ifs with hi
      · exact hi.2.1
      · exact hc.image (continuous_eval i)
    · filter_upwards [J.eventually_cofinite_notMem, hA] with i hi hci
      exact if_pos ⟨hi, hci⟩
    · dsimp only [B]
      split_ifs with hi
      · exact hJ (subset_closure hx) i ⟨hi.1, hi.2.2⟩
      · exact mem_image_of_mem _ (subset_closure hx)
  · rintro ⟨B, hBc, hBA, hH⟩
    let (i : ι) : CompactSpace (B i) := isCompact_iff_compactSpace.mp (hBc i)
    have hbox : ∀ᶠ i in cofinite, ∀ x : (j : ι) → B j, (x i).val ∈ A i :=
      hBA.mono fun i hi x ↦ hi ▸ (x i).2
    let box (x : (i : ι) → B i) : Πʳ i, [G i, A i] :=
      ⟨fun i ↦ x i, hbox.mono fun _ hi ↦ hi x⟩
    have hc : Continuous box := continuous_restrictedProduct_of_uniform
      (fun i ↦ continuous_subtype_val.comp (continuous_apply i)) hbox
    apply (isCompact_range hc).closure_of_subset
    exact fun x hx ↦ ⟨fun i ↦ ⟨x i, hH x hx i⟩, rfl⟩
