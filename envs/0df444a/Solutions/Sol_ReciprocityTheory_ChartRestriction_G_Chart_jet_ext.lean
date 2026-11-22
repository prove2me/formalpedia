-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jet_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:00.585434+00:00
-- url     : https://prove2.me/submissions/ebea0854-0b83-436d-8dc2-f5b03bf86d7b

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
theorem _root_.solution {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] {ψ₁ ψ₂ : JetR R κ m →ₐ[R] A}
    (h : ∀ j, ψ₁ (zR (R := R) m j) = ψ₂ (zR (R := R) m j)) : ψ₁ = ψ₂ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j
end ReciprocityTheory.ChartRestriction.G.Chart
