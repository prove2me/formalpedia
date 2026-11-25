-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:26.268838+00:00
-- url     : https://prove2.me/submissions/cbdec819-597d-474e-a909-d413cf1eecc7

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
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (h : IsParam P U γ) {y : Fin D → ℂ} (hy : y ∈ U) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y :=
  adens_maDensity_nonneg_of hsp h.1 h.2.1 h.2.2.1 hy
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
