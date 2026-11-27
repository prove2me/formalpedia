-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:57.537671+00:00
-- url     : https://prove2.me/submissions/af18ded3-cca4-4715-8fe2-9df2da885392

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_maDensity_nonneg

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) {y : Fin D → ℂ} (hy : y ∈ U) : 0 ≤ adensF m γ ν y := by
  unfold adensF
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  exact div_nonneg (adens_maDensity_nonneg hsp h hy) (mul_pos hD (hν.2.1 y hy)).le
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
