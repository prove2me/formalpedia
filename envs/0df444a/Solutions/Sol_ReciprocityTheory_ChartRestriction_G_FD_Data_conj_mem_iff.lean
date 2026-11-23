-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.conj_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:06.908246+00:00
-- url     : https://prove2.me/submissions/cf504263-76d1-4351-a768-4d1b3c220db1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34

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
theorem _root_.solution (φ : E →+* ℂ) : ComplexEmbedding.conjugate φ ∈ X.Ψ ↔ φ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate φ), conjugate_conjugate']
end ReciprocityTheory.ChartRestriction.G.FD.Data
