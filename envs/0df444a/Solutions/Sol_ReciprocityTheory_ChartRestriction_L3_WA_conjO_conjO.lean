-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.conjO_conjO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:29.797267+00:00
-- url     : https://prove2.me/submissions/796963bf-6e5b-488f-973e-538c9d5dfdff

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_conjO_conjO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution (r : 𝓞 K) : conjO K (conjO K r) = r := ReciprocityTheory.ChartRestriction.L3.conjO_conjO r
end ReciprocityTheory.ChartRestriction.L3.WA
