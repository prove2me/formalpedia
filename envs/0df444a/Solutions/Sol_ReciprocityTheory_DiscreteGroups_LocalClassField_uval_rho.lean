-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.uval_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:21.079005+00:00
-- url     : https://prove2.me/submissions/7705bf34-a3b3-4db9-a12c-976108cf6e1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [(subG p K L).Normal]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (σ : GK p K) (w : (layerU p K L).V) :
    uval ((layerU p K L).rho (QuotientGroup.mk σ) w) = σ (uval w) := rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
