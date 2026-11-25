-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable.compact_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:32.055697+00:00
-- url     : https://prove2.me/submissions/73b3936b-d9d6-4227-8ab8-b407aded57df

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
theorem _root_.solution : ∃ K : Set (X.Ψ → ℝ), IsCompact K ∧ ∀ s, ∃ p ∈ X.periods la, s - p ∈ K := by
  refine ⟨closure (ZSpan.fundamentalDomain (perB X la)),
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure, fun s => ?_⟩
  refine ⟨(ZSpan.floor (perB X la) s : X.Ψ → ℝ), ?_, subset_closure ?_⟩
  · rw [← perB_span X la]
    exact (ZSpan.floor (perB X la) s).prop
  · rw [← ZSpan.fract_apply]
    exact ZSpan.fract_mem_fundamentalDomain _ _
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
