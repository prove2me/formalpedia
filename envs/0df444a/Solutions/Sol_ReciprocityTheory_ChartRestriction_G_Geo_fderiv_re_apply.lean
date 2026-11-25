-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.fderiv_re_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:22.346512+00:00
-- url     : https://prove2.me/submissions/cfe7bab6-47d0-4468-bae2-fdbf4ac61b11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {h : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hh : DifferentiableAt ℂ h y)
    (v : Fin e → ℂ) : fderiv ℝ (fun y' => (h y').re) y v = (fderiv ℂ h y v).re := by
  have hd : HasFDerivAt (fun y' => (h y').re)
      (Complex.reCLM.comp ((fderiv ℂ h y).restrictScalars ℝ)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hh.hasFDerivAt.restrictScalars ℝ)
  rw [hd.fderiv]
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo
