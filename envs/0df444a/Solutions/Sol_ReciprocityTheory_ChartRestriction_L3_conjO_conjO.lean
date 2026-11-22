-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.conjO_conjO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:30.338963+00:00
-- url     : https://prove2.me/submissions/bbe78b4d-45bb-4a96-a55b-0445c29c955b

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_conjO_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  simp only [conjO_coe, star_star]
end ReciprocityTheory.ChartRestriction.L3
