-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.eqOn_Kur
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:27.408711+00:00
-- url     : https://prove2.me/submissions/2ee7d0b5-84b8-46a7-a4dd-39e38b5edcca

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kur_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_eqOn_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_not_dvd_qK_pow_sub_one


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
theorem _root_.solution {σ τ : GK p K} (h : ∀ (ζ : PadicAlgCl p) (m : ℕ), ¬ p ∣ m → ζ ^ m = 1 → σ ζ = τ ζ)
    (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K) : σ x = τ x := by
  obtain ⟨n, hn, hxn⟩ := (mem_Kur_iff hK x).1 hx
  exact UnramifiedExtensions.eqOn_Kn K (fun ζ hζ => h ζ _ (UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn) hζ) hxn
end ReciprocityTheory.DiscreteGroups.LocalClassField
