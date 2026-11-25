-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage.algebraMap_mem_Rv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:02.278704+00:00
-- url     : https://prove2.me/submissions/7a1e0a00-3266-40ab-8e08-bc69a5fd829b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthFraction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
  ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K₁)) (a : 𝓞 K) :
    algebraMap K K₁ (algebraMap (𝓞 K) K a) ∈ Rv K₁ w := by
  have h1 : algebraMap K K₁ (algebraMap (𝓞 K) K a) =
      algebraMap (𝓞 K₁) K₁ (algebraMap (𝓞 K) (𝓞 K₁) a) := by
    first
      | rfl
      | simp [← IsScalarTower.algebraMap_apply]
  rw [h1]
  first
    | exact w.valuation_le_one _
    | exact w.valuation_le_one K₁ _
    | simp [Rv, HeightOneSpectrum.valuationSubringAtPrime, HeightOneSpectrum.valuation_le_one]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
