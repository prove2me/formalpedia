-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fderiv2_lin_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:42:15.802047+00:00
-- url     : https://prove2.me/submissions/a802fa35-89fa-4c73-b9e4-7fcc5c4131dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} (hS : IsOpen S)
    {f g h : E → ℝ} (a b : ℝ) (hf : ContDiffOn ℝ 2 f S) (hg : ContDiffOn ℝ 2 g S)
    (hh : ∀ y ∈ S, h y = a * f y + b * g y) {z : E} (hz : z ∈ S) :
    fderiv ℝ (fderiv ℝ h) z = a • fderiv ℝ (fderiv ℝ f) z + b • fderiv ℝ (fderiv ℝ g) z := by
  have hfz : ∀ y ∈ S, ContDiffAt ℝ 2 f y := fun y hy => hf.contDiffAt (hS.mem_nhds hy)
  have hgz : ∀ y ∈ S, ContDiffAt ℝ 2 g y := fun y hy => hg.contDiffAt (hS.mem_nhds hy)
  have e1 : fderiv ℝ h =ᶠ[𝓝 z] fun y => a • fderiv ℝ f y + b • fderiv ℝ g y := by
    filter_upwards [hS.mem_nhds hz] with y hy
    have hfd : DifferentiableAt ℝ f y := (hfz y hy).differentiableAt (by first | norm_num | simp)
    have hgd : DifferentiableAt ℝ g y := (hgz y hy).differentiableAt (by first | norm_num | simp)
    have hev : h =ᶠ[𝓝 y] fun w => a * f w + b * g w := by
      filter_upwards [hS.mem_nhds hy] with w hw using hh w hw
    exact (((hfd.hasFDerivAt.const_mul a).add (hgd.hasFDerivAt.const_mul b)).congr_of_eventuallyEq hev).fderiv
  rw [e1.fderiv_eq]
  have hf1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hfz z hz).fderiv_right (m := 1) (by first | norm_num | rfl | simp)).differentiableAt (by first | norm_num | simp)
  have hg1 : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((hgz z hz).fderiv_right (m := 1) (by first | norm_num | rfl | simp)).differentiableAt (by first | norm_num | simp)
  exact ((hf1.hasFDerivAt.const_smul a).add (hg1.hasFDerivAt.const_smul b)).fderiv
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
