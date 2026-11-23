-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:12.420964+00:00
-- url     : https://prove2.me/submissions/379e220b-77fd-4f7e-92ef-0d775b148847

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC_zero_left]
end ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
