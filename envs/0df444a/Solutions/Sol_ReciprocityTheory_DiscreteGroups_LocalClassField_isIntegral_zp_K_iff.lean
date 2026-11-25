-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isIntegral_zp_K_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:13:19.321907+00:00
-- url     : https://prove2.me/submissions/6be3d2cd-4fa8-4482-b87e-1ad7d28485ad

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isScalarTower_zp_K_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (x : K) :
    IsIntegral ℤ_[p] x ↔ IsIntegral (PadicInt.subring p) (x : PadicAlgCl p) := by
  have := isScalarTower_zp_K_alg p K
  rw [← isIntegral_algebraMap_iff (A := K) (B := PadicAlgCl p) (algebraMap K (PadicAlgCl p)).injective]
  exact Iff.rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
