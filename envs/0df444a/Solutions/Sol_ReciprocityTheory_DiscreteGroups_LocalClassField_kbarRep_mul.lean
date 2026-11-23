-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.kbarRep_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:11.620388+00:00
-- url     : https://prove2.me/submissions/0ae26a0d-ffb4-45cd-a3b2-3b5bf11b25a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA

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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (σ τ : GK p K) (y : KbarMult p) :
    kbarRep p K (σ * τ) y = kbarRep p K σ (kbarRep p K τ y) := by
  rw [map_mul]; rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
