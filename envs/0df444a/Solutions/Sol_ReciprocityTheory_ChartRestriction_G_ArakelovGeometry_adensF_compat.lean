-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:49.958545+00:00
-- url     : https://prove2.me/submissions/0854e22f-c8f2-40dc-843d-6a3ab17e16c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_density_compare
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_maDensity_compare
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_trans_fac


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
    (hsm : IsSmoothMetric m) {U U' : Set (Fin D → ℂ)} {γ γ' : (Fin D → ℂ) → J → ℂ}
    {ν ν' : (Fin D → ℂ) → ℝ} (h : IsParam P U γ) (hν : IsDensityFor μ U γ ν)
    (h' : IsParam P U' γ') (hν' : IsDensityFor μ U' γ' ν')
    {O' : Set (J → ℂ)} {q' : (J → ℂ) → Fin D → ℂ} (hO' : IsOpen O') (hq' : AnalyticOnNhd ℂ q' O')
    (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {y : Fin D → ℂ} (hy : y ∈ U) (hyO : γ y ∈ O') :
    adensF m γ' ν' (q' (γ y)) * ((D.factorial : ℝ) * ν y) =
      maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  have hτ : q' (γ y) ∈ U' := (adens_trans_fac h.2.2.1 hOP' hsc' hqγ' hy hyO).1
  have e1 := adens_density_compare h hν h'.1 h'.2.1 hν' hO' hq' hOP' hsc' hqγ' hy hyO
  have e2 := adens_maDensity_compare hsm h h'.2.1 hO' hq' hOP' hsc' hqγ' hy hyO
  have hpos : 0 < ν' (q' (γ y)) := hν'.2.1 _ hτ
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  rw [e1, e2]
  unfold adensF
  field_simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
