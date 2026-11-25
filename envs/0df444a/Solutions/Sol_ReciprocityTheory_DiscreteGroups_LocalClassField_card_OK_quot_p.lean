-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.card_OK_quot_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:49:19.656373+00:00
-- url     : https://prove2.me/submissions/4fc994c4-ea48-4fe4-ad1f-cce5e1e1b7a3

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isScalarTower_zp_OK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isTorsionFree_zp_K
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isIntegralClosure_OK
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_card_quot_natCast_padicInt
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_card_quot_span_algebraMap


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) :
    Nat.card (OK p K ⧸ Ideal.span {(p : OK p K)}) = p ^ Module.finrank ℚ_[p] K := by
  have := isScalarTower_zp_OK p K
  have := isIntegralClosure_OK p K
  have := isTorsionFree_zp_K p K
  have : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  have : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  have hr := IsIntegralClosure.rank ℤ_[p] ℚ_[p] K (OK p K)
  have hn' : (p : OK p K) = algebraMap ℤ_[p] (OK p K) (p : ℕ) := (map_natCast _ _).symm
  rw [hn', card_quot_span_algebraMap (Module.finBasis ℤ_[p] (OK p K)),
    card_quot_natCast_padicInt p (Fact.out : p.Prime).ne_zero, Fintype.card_fin, hr, padicValNat_self, pow_one]
end ReciprocityTheory.DiscreteGroups.LocalClassField
