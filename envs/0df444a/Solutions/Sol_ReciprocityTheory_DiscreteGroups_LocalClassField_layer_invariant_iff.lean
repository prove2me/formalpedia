-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.layer_invariant_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:27.472837+00:00
-- url     : https://prove2.me/submissions/42b25c1e-f453-4b50-a8f4-a525b56de0b2

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_multOf_iff_fixed

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
theorem _root_.solution [(subG p K L).Normal] (x : (layer p K L).V) :
    (∀ g, (layer p K L).rho g x = x) ↔ x.1 ∈ multOf p K := by
  refine Iff.trans ?_ (mem_multOf_iff_fixed (le_refl K) x.1).symm
  constructor
  · intro hx σ _
    exact congrArg Subtype.val (hx (QuotientGroup.mk σ))
  · intro hx g
    induction g using QuotientGroup.induction_on with
    | H σ => exact Subtype.ext (hx σ fun y hy => σ.commutes ⟨y, hy⟩)
end ReciprocityTheory.DiscreteGroups.LocalClassField
