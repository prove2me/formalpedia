-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.admissible_int_rat_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:46.170819+00:00
-- url     : https://prove2.me/submissions/46b135f7-64da-4e4e-8359-00699f9ee97c

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
theorem _root_.solution : admitted (trivMap G (Int.castAddHom ℚ)) (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)) where
  i_id := rfl
  p_id := rfl
  emb := by
    have hi : Injective (trivMap G (Int.castAddHom ℚ)).u := Int.cast_injective (α := ℚ)
    exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology hi
      fun _ _ => isOpen_discrete _).isEmbedding
  exact := by
    intro (y : ℚ)
    show (QuotientAddGroup.mk y : QZ) = 0 ↔ y ∈ Set.range (Int.castAddHom ℚ)
    rw [QuotientAddGroup.eq_zero_iff]; rfl
  sec := ⟨Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range),
    continuous_of_discreteTopology, Function.surjInv_eq _⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
