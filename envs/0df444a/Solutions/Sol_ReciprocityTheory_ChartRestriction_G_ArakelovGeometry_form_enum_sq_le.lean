-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.form_enum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:14:11.142804+00:00
-- url     : https://prove2.me/submissions/35a1dbb8-0fde-4d98-ba66-aa7a820fa570

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adtEnum_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_adtEnum
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_form_sq_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_form_sq
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
theorem _root_.solution (D N : ℕ) (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℂ)
    (w : Fin (D + 1) → ℂ) :
    ‖∑ i, c i * monoC (adtEnum D N i) w‖ ^ 2 ≤ ((N + D).choose D : ℝ) * sqN w ^ N *
      ∑ i, ‖c i‖ ^ 2 * monoNormSq (adtEnum D N i) := by
  classical
  set c' : (Fin (D + 1) → ℕ) → ℂ := fun a => if h : a ∈ Finset.Nat.antidiagonalTuple (D + 1) N then
    c ((Finset.Nat.antidiagonalTuple (D + 1) N).equivFin ⟨a, h⟩) else 0 with hc'
  have hci : ∀ i, c' (adtEnum D N i) = c i := fun i => by
    simp only [hc', dif_pos (adtEnum_mem D N i)]
    simp [adtEnum]
  have e1 : ∑ i, c i * monoC (adtEnum D N i) w =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, c' a * monoC a w := by
    rw [← sum_adtEnum D N (fun a => c' a * monoC a w)]
    simp only [hci]
  have e2 : ∑ i, ‖c i‖ ^ 2 * monoNormSq (adtEnum D N i) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, ‖c' a‖ ^ 2 * monoNormSq a := by
    rw [← sum_adtEnum D N (fun a => ‖c' a‖ ^ 2 * monoNormSq a)]
    simp only [hci]
  rw [e1, e2, ← integral_form_sq]
  exact form_sq_le D N c' w
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
