-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_crd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:46.726977+00:00
-- url     : https://prove2.me/submissions/7e7a6926-5083-4a08-b86b-888f9eac51af

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
    (hb : IsSecBasis x n b) :
    ∃ crd : sec ℤ x n →ₗ[ℤ] (Fin r → ℤ),
      (∀ v : sec ℤ x n, ∑ j, (crd v j : Ω) * aeval x (b j) = v) ∧
      ∀ j (h : aeval x (b j) ∈ sec ℤ x n), crd ⟨aeval x (b j), h⟩ = Pi.single j 1 := by
  classical
  set bas := (Basis.span hb.2.1).map (LinearEquiv.ofEq _ _ hb.2.2) with hbas
  have hbj : ∀ j, (bas j : Ω) = aeval x (b j) := fun j => by
    simp [hbas, Basis.span_apply]
  refine ⟨(Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r)).toLinearMap ∘ₗ bas.repr.toLinearMap,
    fun v => ?_, fun j h => ?_⟩
  · conv_rhs => rw [← bas.sum_repr v]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, hbj, zsmul_eq_mul]
    rfl
  · have : (⟨aeval x (b j), h⟩ : sec ℤ x n) = bas j := Subtype.ext (hbj j).symm
    rw [this]
    simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
