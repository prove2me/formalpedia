-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:52.763485+00:00
-- url     : https://prove2.me/submissions/25f0572a-2643-485f-972b-e1ef8b82fa73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_continuousOn_maDens
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__a466d063bccb


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
theorem _root_.solution {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    {μ : Measure (J → ℂ)} (hsm : IsSmoothMetric m) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) : ContinuousOn (adensF m γ ν) U := by
  obtain ⟨hU, hγ, hpts, -⟩ := h
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hMA : ContinuousOn (maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w)))) U := by
    refine adens_continuousOn_maDens _ hU fun _ => ?_
    intro y hy
    exact (adens_contDiffAt_logρ hsm (hγ y hy) (hpts y hy).1).contDiffWithinAt
  exact hMA.div (continuousOn_const.mul hν.1.continuousOn) fun y hy =>
    (mul_pos hD (hν.2.1 y hy)).ne'
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
