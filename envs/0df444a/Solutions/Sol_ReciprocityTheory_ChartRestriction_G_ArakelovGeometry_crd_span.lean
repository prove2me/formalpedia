-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.crd_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:30.913783+00:00
-- url     : https://prove2.me/submissions/9110d479-21dc-4d1b-ae5c-c38807e55a4a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    {crd : sec ℤ x n →ₗ[ℤ] (Fin r → ℤ)}
    (hcrd : ∀ j (h : aeval x (b j) ∈ sec ℤ x n), crd ⟨aeval x (b j), h⟩ = Pi.single j 1)
    (hb : IsSecBasis x n b) {ι : Type} (w : ι → Ω) (hw : ∀ s, w s ∈ sec ℤ x n)
    (hle : sec ℤ x n ≤ Submodule.span ℤ (Set.range w)) (v : Fin r → ℤ) :
    v ∈ Submodule.span ℤ (Set.range fun s => crd ⟨w s, hw s⟩) := by
  have hsub : Submodule.span ℤ (Set.range w) ≤ sec ℤ x n :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hw)
  have key : ∀ y (hy : y ∈ Submodule.span ℤ (Set.range w)),
      crd ⟨y, hsub hy⟩ ∈ Submodule.span ℤ (Set.range fun s => crd ⟨w s, hw s⟩) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      exact Submodule.subset_span ⟨s, rfl⟩
    | zero =>
      have : (⟨0, hsub (Submodule.zero_mem _)⟩ : sec ℤ x n) = 0 := rfl
      rw [this, map_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ h₁ h₂ ih₁ ih₂ =>
      have : (⟨y₁ + y₂, hsub (Submodule.add_mem _ h₁ h₂)⟩ : sec ℤ x n) =
          ⟨y₁, hsub h₁⟩ + ⟨y₂, hsub h₂⟩ := rfl
      rw [this, map_add]; exact Submodule.add_mem _ ih₁ ih₂
    | smul a y h ih =>
      have : (⟨a • y, hsub (Submodule.smul_mem _ a h)⟩ : sec ℤ x n) = a • ⟨y, hsub h⟩ := rfl
      rw [this, map_smul]; exact Submodule.smul_mem _ _ ih
  have hbm : ∀ j, aeval x (b j) ∈ sec ℤ x n := fun j => hb.2.2 ▸ Submodule.subset_span ⟨j, rfl⟩
  have hv : v = ∑ j, v j • crd ⟨aeval x (b j), hbm j⟩ := by
    simp only [hcrd]
    funext q
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (key _ (hle (hbm j)))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
