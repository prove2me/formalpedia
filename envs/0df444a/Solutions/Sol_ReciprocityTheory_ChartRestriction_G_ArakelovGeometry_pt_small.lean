-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pt_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:40.118411+00:00
-- url     : https://prove2.me/submissions/b85d0207-4139-4a9e-a600-3f60964304a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eval_prodForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_norm_monoC_sq_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sqN_comp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sq_wgt_le_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {N k₀ : ℕ} {a : Fin (D + 1) → ℕ} (ha : ∑ t, a t = N)
    (t : MvPolynomial (Ix κ) ℤ) {Ct : ℝ}
    (hCt : ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z (map (Int.castRingHom ℂ) t)‖ ≤ Ct * m.ρ z ^ k₀)
    {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    ‖eval z (map (Int.castRingHom ℂ) (prodForm e a t))‖ ^ 2 * wgt m (N + k₀) z ≤ Ct ^ 2 := by
  have hρ0 : 0 ≤ m.ρ z := m.nonneg z
  have hm : ‖monoC a (z ∘ e)‖ ≤ m.ρ z ^ N := by
    have h := norm_monoC_sq_le a (z ∘ e)
    have e2 : (m.ρ z ^ 2) ^ N = (m.ρ z ^ N) ^ 2 := by ring
    rw [sqN_comp_eq hFS hz, ha, e2] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (pow_nonneg hρ0 N) two_ne_zero).mp h
  refine sq_wgt_le_of_le hz.1 (norm_nonneg _) ?_
  rw [eval_prodForm, norm_mul]
  have h2 := hCt z hz
  calc ‖monoC a (z ∘ e)‖ * ‖eval z (map (Int.castRingHom ℂ) t)‖ ≤ m.ρ z ^ N * (Ct * m.ρ z ^ k₀) :=
        mul_le_mul hm h2 (norm_nonneg _) (pow_nonneg hρ0 N)
    _ = Ct * m.ρ z ^ (N + k₀) := by ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
