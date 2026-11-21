-- Prove2me | solution 1 for RiemannMasullo.restrictedProduct_description
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:29:28.959914+00:00
-- url     : https://prove2.me/submissions/c1619388-3337-49a3-b25d-8971f615036f

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L54-L105
import Theorems.Thm_RiemannMasullo_isOpen_restrictedProduct_forall_mem
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
    Set.range (fun x : Πʳ i, [G i, K i] ↦ fun i ↦ x i) =
      {x | ∀ᶠ i in cofinite, x i ∈ K i} ∧
    (𝓝 (1 : Πʳ i, [G i, K i])).HasBasis
      (fun U : (i : ι) → Set (G i) ↦ (∀ i, U i ∈ 𝓝 1) ∧ ∀ᶠ i in cofinite, U i = K i)
      (fun U ↦ {x | ∀ i, x i ∈ U i}) := by
  classical
  refine ⟨RestrictedProduct.range_coe G _, hasBasis_iff.mpr fun T ↦ ⟨?_, ?_⟩⟩
  · intro hT
    let S : Set ι := {i | i ∉ I₀}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr I₀.eventually_cofinite_notMem
    let f := RestrictedProduct.inclusion G (fun i ↦ (K i : Set (G i))) hS
    have hT' : f ⁻¹' T ∈ 𝓝 (1 : Πʳ i, [G i, K i]_[𝓟 S]) :=
      (RestrictedProduct.continuous_inclusion hS).continuousAt hT
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isInducing.nhds_eq_comap] at hT'
    obtain ⟨W, hW, hWT⟩ := mem_comap.mp hT'
    rw [nhds_pi, Filter.mem_pi'] at hW
    obtain ⟨J, V, hV, hVW⟩ := hW
    let U (i : ι) := (if i ∈ J then V i else Set.univ) ∩
      (if i ∈ I₀ then Set.univ else (K i : Set (G i)))
    refine ⟨U, ⟨fun i ↦ inter_mem ?_ ?_, ?_⟩, ?_⟩
    · by_cases hi : i ∈ J
      · simpa only [if_pos hi, RestrictedProduct.one_apply] using hV i
      · simp [hi]
    · by_cases hi : i ∈ I₀
      · simp [hi]
      · simpa [hi] using (h₁ i hi).2.mem_nhds (K i).one_mem
    · filter_upwards [J.eventually_cofinite_notMem, I₀.eventually_cofinite_notMem] with i hiJ hi₀
      simp [U, hiJ, hi₀]
    · intro x hx
      let y : Πʳ i, [G i, K i]_[𝓟 S] :=
        ⟨x, fun i hi ↦ by simpa [U, show i ∉ I₀ from hi] using (hx i).2⟩
      have hy : (fun i ↦ y i) ∈ (J : Set ι).pi V := by
        intro i hi
        change x i ∈ V i
        simpa [U, Finset.mem_coe.mp hi] using (hx i).1
      exact hWT (hVW hy)
  · rintro ⟨U, ⟨hU, hUK⟩, hUT⟩
    let S : Set ι := {i | i ∉ I₀ ∧ U i = K i}
    have hS : S ∈ (cofinite : Filter ι) := I₀.eventually_cofinite_notMem.and hUK
    have hTail := (isOpen_restrictedProduct_forall_mem S (fun i hi ↦ (h₁ i hi.1).2)).mem_nhds
      (x := (1 : Πʳ i, [G i, K i])) (fun i _ ↦ (K i).one_mem)
    have hFinite : Sᶜ.pi U ∈ 𝓝 (fun i ↦ (1 : G i)) :=
      set_pi_mem_nhds (mem_cofinite.mp hS) (fun i _ ↦ hU i)
    refine mem_of_superset (inter_mem hTail
      (RestrictedProduct.continuous_coe.continuousAt hFinite)) ?_
    intro x hx
    apply hUT
    intro i
    by_cases hi : i ∈ S
    · exact hi.2.symm ▸ hx.1 i hi
    · exact hx.2 i hi
