-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_nonneg_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:26:01.75881+00:00
-- url     : https://prove2.me/submissions/38349df7-5d19-4387-9bff-415f7564220b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_maDensity_nonneg_of

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
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {γ : (Fin D → ℂ) → J → ℂ}
    {y : Fin D → ℂ} (hγ : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' ∧ γ y' ∈ pts P) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  obtain ⟨s, hs, hsγ⟩ := hγ.exists_mem
  obtain ⟨V, hVs, hV, hyV⟩ := mem_nhds_iff.1 hs
  exact adens_maDensity_nonneg_of hsp hV (fun w hw => (hsγ w (hVs hw)).1)
    (fun w hw => (hsγ w (hVs hw)).2) hyV
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
