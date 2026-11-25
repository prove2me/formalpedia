-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_of_frobK_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:54:12.623058+00:00
-- url     : https://prove2.me/submissions/cde04fbb-0447-41e8-adaa-741c5d4f3dfe

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kur_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrob_frobK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrob_isFrobOn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_exists_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_of_fixed


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K)
    (h : frobK p K x = x) : x ∈ K := by
  obtain ⟨n, hn, hxn⟩ := (mem_Kur_iff hK x).1 hx
  apply UnramifiedExtensions.mem_of_fixed K
  intro σ
  obtain ⟨i, -, hi⟩ := IsFrobOn.exists_pow p K hK hn ((isFrob_frobK hK).isFrobOn n) σ
  rw [hi x hxn]
  clear hi
  induction i with
  | zero => rfl
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
end ReciprocityTheory.DiscreteGroups.LocalClassField
