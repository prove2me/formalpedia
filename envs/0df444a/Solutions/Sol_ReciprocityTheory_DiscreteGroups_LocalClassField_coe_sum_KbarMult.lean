-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.coe_sum_KbarMult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:06:47.91496+00:00
-- url     : https://prove2.me/submissions/b120136e-c9e2-4a1f-a2a2-3fd9144dcef1

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA

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
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → KbarMult p) :
    ((Additive.toMul (∑ c ∈ s, f c) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ∏ c ∈ s, ((Additive.toMul (f c) : (PadicAlgCl p)ˣ) : PadicAlgCl p) := by
  let F : KbarMult p →+ Additive (PadicAlgCl p) :=
    { toFun := fun x => Additive.ofMul ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h2 := congrArg Additive.toMul (map_sum F f s)
  rw [toMul_sum] at h2
  exact h2
end ReciprocityTheory.DiscreteGroups.LocalClassField
