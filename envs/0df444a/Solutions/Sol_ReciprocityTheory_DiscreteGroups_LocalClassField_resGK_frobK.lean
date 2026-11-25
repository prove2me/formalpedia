-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.resGK_frobK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:43:37.072643+00:00
-- url     : https://prove2.me/submissions/195841fd-8ad4-4d87-939e-1621de8c9bc6

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eqOn_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrob_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrob_frobK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_frobLK_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrob_pow_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_resGK_apply


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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) {f : ℕ}
    (hf : qK p L = qK p K ^ f) :
    (QuotientGroup.mk (resGK h (frobK p L)) : GalLK p K (MaximalUnramifiedExtension p K)) = frobLK p K (MaximalUnramifiedExtension p K) ^ f := by
  rw [frobLK_pow, mk_eq_mk_iff]
  intro x hx
  refine eqOn_Kur (fun ζ m hm hζ => ?_) hK hx
  rw [resGK_apply, (isFrob_iff hL _).1 (isFrob_frobK hL) ζ m hm hζ, hf,
    IsFrob.pow_apply hK (isFrob_frobK hK) hm f hζ]
end ReciprocityTheory.DiscreteGroups.LocalClassField
