-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.uval_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:40.301548+00:00
-- url     : https://prove2.me/submissions/1e1da5e6-cf21-44fd-ae25-9639772dd86b

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
theorem _root_.solution (a : (layerU p K L).V) : uval (-a) = (uval a)⁻¹ := Units.val_inv_eq_inv_val _
end ReciprocityTheory.DiscreteGroups.LocalClassField
