-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.ip_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:12.543152+00:00
-- url     : https://prove2.me/submissions/46529c52-7320-4c00-ad38-c36f32e2e982

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
open Matrix NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
theorem _root_.solution (u : X.Ψ → Fin r → ℂ) : ip X u u = ∑ τ, X.c τ * ∑ a, ‖u τ a‖ ^ 2 := by
  unfold ip
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
