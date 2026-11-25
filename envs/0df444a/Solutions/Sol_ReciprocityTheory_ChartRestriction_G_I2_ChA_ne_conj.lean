-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.ne_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:41.526996+00:00
-- url     : https://prove2.me/submissions/fc467647-6c32-4995-a287-7922ea004a43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA
namespace ReciprocityTheory.ChartRestriction.G.I2.ChA
theorem _root_.solution [IsCMField E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hc := NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk σ)
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  exact hc (ComplexEmbedding.isReal_iff.mpr h)
end ReciprocityTheory.ChartRestriction.G.I2.ChA
