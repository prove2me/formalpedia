-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.charGrp_eval_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:48.444798+00:00
-- url     : https://prove2.me/submissions/787f8983-7156-4b78-bd06-1a58ec0dedd6

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (s : G) (hs : Dense (Subgroup.zpowers s : Set G)) :
    Injective fun χ : charGrp G => χ.1 (Additive.ofMul s) := by
  have key : ∀ ψ : charGrp G, ψ.1 (Additive.ofMul s) = 0 → ψ = 0 := by
    intro ψ h
    have hcl : IsClosed {g : G | ψ.1 (Additive.ofMul g) = 0} := (IsLocallyConstant.isClopen_fiber ψ.2 0).1
    have hsub : (Subgroup.zpowers s : Set G) ⊆ {g : G | ψ.1 (Additive.ofMul g) = 0} := by
      rintro _ ⟨k, rfl⟩
      show ψ.1 (Additive.ofMul (s ^ k)) = 0
      rw [ofMul_zpow, map_zsmul, h, smul_zero]
    have hall := closure_minimal hsub hcl
    rw [hs.closure_eq] at hall
    exact Subtype.ext (AddMonoidHom.ext fun a => hall (Set.mem_univ a.toMul))
  intro χ χ' h
  refine sub_eq_zero.1 (key (χ - χ') ?_)
  show χ.1 (Additive.ofMul s) - χ'.1 (Additive.ofMul s) = 0
  exact sub_eq_zero.2 h
end ReciprocityTheory.DiscreteGroups.LocalClassField
