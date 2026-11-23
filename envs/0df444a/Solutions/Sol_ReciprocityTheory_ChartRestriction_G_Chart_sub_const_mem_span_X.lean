-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.sub_const_mem_span_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:40.049549+00:00
-- url     : https://prove2.me/submissions/9906de53-df3a-44d9-ba06-e035bc0b933f

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
theorem _root_.solution {κ : Type} (p : MvPolynomial κ R) :
    p - MvPolynomial.C (MvPolynomial.aeval (fun _ : κ => (0 : R)) p) ∈
      Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) := by
  classical
  have hs : Set.range (MvPolynomial.X : κ → MvPolynomial κ R) = MvPolynomial.X '' Set.univ := by
    rw [Set.image_univ]
  rw [hs, MvPolynomial.mem_ideal_span_X_image]
  intro mono hm
  by_contra hcon
  push Not at hcon
  have h0 : mono = 0 := by
    ext i
    exact hcon i (Set.mem_univ i)
  subst h0
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl] at hm
  apply hm
  rw [sub_eq_zero, MvPolynomial.aeval_zero', ← MvPolynomial.constantCoeff_eq]
  rfl
end ReciprocityTheory.ChartRestriction.G.Chart
