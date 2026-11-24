-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.absNorm_span_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:38.22195+00:00
-- url     : https://prove2.me/submissions/70206431-6ba6-43e5-a5af-ba7110d65b22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution (ℓ : ℕ) : Ideal.absNorm (Ideal.span {(ℓ : 𝓞 E)}) = ℓ ^ Module.finrank ℚ E := by
  rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap,
    NumberField.RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
