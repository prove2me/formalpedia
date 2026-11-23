-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_multOf_iff_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:30.093582+00:00
-- url     : https://prove2.me/submissions/17617e4d-80f8-46ec-8d44-0f6bd5ae04a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_iff_fixed

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
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) (x : KbarMult p) :
    x ∈ multOf p L ↔ ∀ σ ∈ subG p K L, kbarRep p K σ x = x := by
  have h1 : x ∈ multOf p L ↔ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) ∈ L := Iff.rfl
  rw [h1, mem_iff_fixed h]
  refine forall₂_congr fun σ _ => ⟨fun hx => Units.ext hx, fun hx => ?_⟩
  exact congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) hx
end ReciprocityTheory.DiscreteGroups.LocalClassField
