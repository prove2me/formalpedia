-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion.exists_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:28.490951+00:00
-- url     : https://prove2.me/submissions/c01a95a1-b559-4819-b267-dc2698bdab54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) :
    ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ := by
  let L : Submodule ℤ (X.Ψ → ℝ) := (X.periods la).toIntSubmodule
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (X.periods la))
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using RealEmbeddingCharacters.periods_span (X := X) (la := la)⟩
  haveI := ZLattice.module_free ℝ L
  haveI := ZLattice.module_finite ℝ L
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := by
    show Submodule.span ℤ (Set.range ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) = L
    rw [Module.Basis.ofZLatticeBasis_span]
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain b volume
    rw [hspan] at h
    exact h
  · exact pos_iff_ne_zero.2 (ZSpan.measure_fundamentalDomain_ne_zero b)
  · exact (ZSpan.fundamentalDomain_isBounded b).measure_lt_top
end ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
