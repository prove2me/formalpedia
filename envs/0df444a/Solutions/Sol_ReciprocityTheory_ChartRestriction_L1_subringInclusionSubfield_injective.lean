-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.subringInclusionSubfield_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:13.481457+00:00
-- url     : https://prove2.me/submissions/31d49132-8759-440d-a87b-0a30d6441718

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_subringInclusionSubfield_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : Function.Injective (subringInclusionSubfield R F h) := fun x y e =>
  Subtype.ext (by rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, e])
end ReciprocityTheory.ChartRestriction.L1
