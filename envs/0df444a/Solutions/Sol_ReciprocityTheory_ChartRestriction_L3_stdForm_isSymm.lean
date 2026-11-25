-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.stdForm_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:38.97984+00:00
-- url     : https://prove2.me/submissions/51b3309f-aaa5-42cc-af02-e9ae16985f3e

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_stdForm_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (K : Type) [Field K] [StarRing K] (n : ℕ) : (stdForm K n).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp [stdForm_apply, mul_comm, starRingEnd_apply]
end ReciprocityTheory.ChartRestriction.L3
