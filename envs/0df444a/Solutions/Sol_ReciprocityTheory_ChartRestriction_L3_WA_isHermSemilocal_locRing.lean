-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.isHermSemilocal_locRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:10:03.960177+00:00
-- url     : https://prove2.me/submissions/6eae4f19-dd16-4225-8a01-971820fe6f87

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_IsHermSemilocalLocRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_principal_locRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_unit_or_locRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_frac_locRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_star_mem_locRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_unram_locRing


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) where
  star_mem := fun _ ha => star_mem_locRing hp.isPrime ha
  frac := frac_locRing p
  unram := unram_locRing hK hp
  principal := principal_locRing hK hp
  unit_or := fun a ha κ hκ μ hna hμ => unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ
end ReciprocityTheory.ChartRestriction.L3.WA
