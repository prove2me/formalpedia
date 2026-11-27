-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sec_le_span_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:26:20.70244+00:00
-- url     : https://prove2.me/submissions/83769bd5-54f2-40fb-ae07-1d77abe89209

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_eq_sum_adt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_map_intQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_prodForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_adtEnum
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
theorem _root_.solution {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {n k₀ r₀ : ℕ}
    (hmul : sec ℤ x n = sec ℤ (x ∘ e) (n - k₀) * sec ℤ x k₀) {tb : Fin r₀ → MvPolynomial (Ix κ) ℚ}
    (htb : IsSecBasis x k₀ tb) (Tf : Fin r₀ → MvPolynomial (Ix κ) ℤ)
    (hTfb : ∀ i, tb i = map (Int.castRingHom ℚ) (Tf i)) :
    sec ℤ x n ≤ Submodule.span ℤ (Set.range fun s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card ×
      Fin r₀ => aeval x (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2))) := by
  rw [hmul, Submodule.mul_le]
  intro a ha t ht
  obtain ⟨pa, hpa, rfl⟩ := Submodule.mem_map.mp ha
  have hpa' : pa.IsHomogeneous (n - k₀) := (mem_homogeneousSubmodule _ _).mp hpa
  rw [← htb.2.2, Submodule.mem_span_range_iff_exists_fun] at ht
  obtain ⟨cc, rfl⟩ := ht
  have ea : (aeval (x ∘ e)).toLinearMap pa = ∑ i, (coeff (Finsupp.equivFunOnFinite.symm
      (adtEnum D (n - k₀) i)) pa : ℤ) • ∏ t, (x ∘ e) t ^ adtEnum D (n - k₀) i t := by
    rw [AlgHom.toLinearMap_apply, aeval_eq_sum_adt pa hpa', ← sum_adtEnum]
    simp only [zsmul_eq_mul]
  rw [ea, Finset.sum_mul_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun i₀ _ => ?_
  have : (coeff (Finsupp.equivFunOnFinite.symm (adtEnum D (n - k₀) i)) pa : ℤ) •
      (∏ t, (x ∘ e) t ^ adtEnum D (n - k₀) i t) * cc i₀ • aeval x (tb i₀) =
      (coeff (Finsupp.equivFunOnFinite.symm (adtEnum D (n - k₀) i)) pa * cc i₀) •
        aeval x (prodForm e (adtEnum D (n - k₀) i) (Tf i₀)) := by
    rw [aeval_prodForm, hTfb i₀, aeval_map_intQ]
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, i₀), rfl⟩)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
