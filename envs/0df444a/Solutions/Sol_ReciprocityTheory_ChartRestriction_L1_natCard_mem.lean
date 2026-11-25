-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.natCard_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:19.140772+00:00
-- url     : https://prove2.me/submissions/d05ac0a2-3945-416c-9cbc-6da7c0c891c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLatTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModCMPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobCong

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 E)} (h : LiesAbove A v) :
    ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : Ω) ∈ A.nonunits := by
  have hmem : ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    rcases finite_or_infinite (𝓞 E ⧸ v.asIdeal) with hf | hf
    · have := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero _
    · rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero]
  have h2 := (h _).mpr hmem
  simpa using h2
end ReciprocityTheory.ChartRestriction.L1
