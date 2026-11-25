-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isDedekindDomain_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:48.769639+00:00
-- url     : https://prove2.me/submissions/b71ac2db-e54b-4b6e-90b6-ca66bf90600d

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isScalarTower_zp_OK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isIntegralClosure_OK

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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) : IsDedekindDomain (OK p K) := by
  have := isScalarTower_zp_OK p K
  have := isIntegralClosure_OK p K
  exact IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K (OK p K)
end ReciprocityTheory.DiscreteGroups.LocalClassField
