-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sec_eq_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:25.753344+00:00
-- url     : https://prove2.me/submissions/8f8f2272-d3fd-43be-969d-579720192f6d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
private theorem section_module_eq_span_pow (x : κ → Ω) (n : ℕ) :
    sec ℤ x n = (Submodule.span ℤ (Set.range x)) ^ n := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp]
  congr 2
  ext i
  simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (n : ℕ) :
    sec ℤ x n = (Submodule.span ℤ (Set.range x)) ^ n :=
  section_module_eq_span_pow x n
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
