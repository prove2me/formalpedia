-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.norm_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:31.055255+00:00
-- url     : https://prove2.me/submissions/c79d22ab-33ad-4ee2-811e-855f1e91c15b

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA

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
variable {p}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : E →ₐ[ℚ_[p]] PadicAlgCl p) (x : E) :
    ‖σ x‖ = ‖(x : PadicAlgCl p)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq E.val E.val.injective]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
