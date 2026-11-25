-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable.fd_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:35.717508+00:00
-- url     : https://prove2.me/submissions/4b369195-7391-4859-9c8e-836af6741562

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodLatticeCountable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PeriodLatticeCountable_perB_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (la : Wt X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
theorem _root_.solution : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧
    IsAddFundamentalDomain (X.periods la) D volume ∧ 0 < volume D ∧ volume D < ⊤ := by
  refine ⟨ZSpan.fundamentalDomain (perB X la), ZSpan.fundamentalDomain_measurableSet _, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain (perB X la) volume
    rw [← perB_span X la]
    exact h
  · exact pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero _)
  · exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
