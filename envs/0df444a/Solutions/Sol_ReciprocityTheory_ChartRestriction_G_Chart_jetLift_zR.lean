-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jetLift_zR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:11.897817+00:00
-- url     : https://prove2.me/submissions/81f21c15-1696-4ab4-a77b-2a039f42adb6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open MvPolynomial
variable (R : Type) [CommRing R]
variable {R}
variable (R)
variable {R}
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] (J : Ideal A)
    (hJ : J ^ (m + 1) = ⊥) (b : κ → A) (hb : ∀ j, b j ∈ J) (j : κ) :
    jetLift R J hJ b hb (zR m j) = b j := by
  show MvPolynomial.aeval b (MvPolynomial.X j) = b j
  simp
end ReciprocityTheory.ChartRestriction.G.Chart
