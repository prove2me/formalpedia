-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:57.489866+00:00
-- url     : https://prove2.me/submissions/503e41a0-eb1b-45d7-a320-e8d0027b22c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
end ReciprocityTheory.ChartRestriction.G.FD.Data
