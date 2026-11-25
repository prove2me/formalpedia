-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.eqOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:58.383677+00:00
-- url     : https://prove2.me/submissions/56cbde38-0396-4d57-a6fe-d6d3b92c2d0b

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrobOn_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_eqOn_Kn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
namespace IsFrobOn
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ ψ : GK p K}
    (hφ : IsFrobOn p K n φ) (hψ : IsFrobOn p K n ψ) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) :
    φ x = ψ x := by
  rw [isFrobOn_iff p K hK hn] at hφ hψ
  exact UnramifiedExtensions.eqOn_Kn K (fun ζ hζ => by rw [hφ ζ hζ, hψ ζ hζ]) hx
end IsFrobOn
end ReciprocityTheory.DiscreteGroups.LocalClassField
