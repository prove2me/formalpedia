-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sum_mulVec_secFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:28:01.102803+00:00
-- url     : https://prove2.me/submissions/33ac3454-4d91-4697-8326-00856a31ef39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_secFun_eq__d81f0b965cfc
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
theorem _root_.solution {x : Ix κ → Ω} {n r R : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) (M : Matrix (Fin r) (Fin R) ℤ) (Q : Fin R → MvPolynomial (Ix κ) ℤ)
    (hQ : ∀ p, (Q p).IsHomogeneous n)
    (hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) = aeval x (Q p)) (c : Fin R → ℂ) :
    ∀ z ∈ pts (coordIdeal ℤ x), ∑ j, (M.map (Int.cast : ℤ → ℂ) *ᵥ c) j * secFun (b j) z =
      ∑ p, c p * eval z (map (Int.castRingHom ℂ) (Q p)) := by
  intro z hz
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← sum_secFun_eq' hb (Q p) (hQ p) (fun j => M j p) (hM p) z hz, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
