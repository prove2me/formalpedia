-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.ip_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:03.082544+00:00
-- url     : https://prove2.me/submissions/bde6cf9a-33c4-458b-a962-a869f54196f8

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
theorem _root_.solution (u w : X.Ψ → Fin r → ℂ) : ip X u w = ip X w u := by
  unfold ip
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
