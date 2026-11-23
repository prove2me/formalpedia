-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_normGrp_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:54.612133+00:00
-- url     : https://prove2.me/submissions/f623b9b3-703e-4bef-8c7b-7eb0f34bde22

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (x : Kˣ) :
    x ∈ normGrp p K L ↔ ∃ y ∈ multOf p L, normHom p K L y = ofK p K (Additive.ofMul x) := Iff.rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
