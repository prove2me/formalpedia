-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrob.eqOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:18:18.987506+00:00
-- url     : https://prove2.me/submissions/fa636090-41af-4719-bb1f-78e4d4272414

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eqOn_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrob_iff

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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {σ τ : GK p K} (hσ : IsFrob p K σ) (hτ : IsFrob p K τ)
    {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K) : σ x = τ x :=
  eqOn_Kur (fun ζ m hm hζ => by rw [(isFrob_iff hK σ).1 hσ ζ m hm hζ, (isFrob_iff hK τ).1 hτ ζ m hm hζ]) hK hx
end IsFrob
end ReciprocityTheory.DiscreteGroups.LocalClassField
