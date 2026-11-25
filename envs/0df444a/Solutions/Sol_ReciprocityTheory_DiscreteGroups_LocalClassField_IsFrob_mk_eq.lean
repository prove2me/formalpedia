-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrob.mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:14.229028+00:00
-- url     : https://prove2.me/submissions/1b179269-77df-44fe-9f5e-d053ce23b474

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrob_frobK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrob_eqOn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_eqOn


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
namespace IsFrob
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {σ : GK p K} (h : IsFrob p K σ) :
    (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) = frobLK p K (MaximalUnramifiedExtension p K) :=
  (mk_eq_mk_iff σ (frobK p K)).2 fun _ hx => IsFrob.eqOn hK h (isFrob_frobK hK) hx
end IsFrob
end ReciprocityTheory.DiscreteGroups.LocalClassField
