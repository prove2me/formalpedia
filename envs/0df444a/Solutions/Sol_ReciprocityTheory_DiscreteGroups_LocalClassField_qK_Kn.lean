-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.qK_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:10:55.267328+00:00
-- url     : https://prove2.me/submissions/f8894b72-4bb1-4c73-9a64-b315eaa6870e

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_unramified_extension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    qK p (Kn p K n) = qK p K ^ n :=
  (finrank_unramified_extension p K hK hn).2
end ReciprocityTheory.DiscreteGroups.LocalClassField
