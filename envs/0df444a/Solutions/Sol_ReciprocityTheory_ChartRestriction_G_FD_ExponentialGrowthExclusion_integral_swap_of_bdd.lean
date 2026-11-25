-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion.integral_swap_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:33.318839+00:00
-- url     : https://prove2.me/submissions/a14f82a3-b259-45b4-9f16-acbd7a3d7a9a

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
theorem _root_.solution {m n : Type} [Fintype m] [Fintype n] {D : Set (m → ℝ)} {K : Set (n → ℝ)}
    (hD : volume D < ⊤) (hK : volume K < ⊤) {f : (m → ℝ) → (n → ℝ) → ℂ}
    (hf : Continuous (Function.uncurry f)) {M : ℝ} (hM : ∀ s t, ‖f s t‖ ≤ M) :
    ∫ s in D, ∫ t in K, f s t = ∫ t in K, ∫ s in D, f s t := by
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.2 hD.ne
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.ne
  apply MeasureTheory.integral_integral_swap
  exact Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hM p.1 p.2)
end ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
