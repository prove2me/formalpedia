-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_normal_index_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:26.596656+00:00
-- url     : https://prove2.me/submissions/34739fad-7943-4c62-b735-2fc507d67670

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_SubsingletonHOfSubsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_exists_normal_index


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open ReciprocityTheory.Coh Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {H : Type*} [Group H] [Finite H] [Nontrivial H] (l : ℕ) [Fact l.Prime]
    (hH : IsPGroup l H) : ∃ N : Subgroup H, N.Normal ∧ N.index = l :=
  Deg2.exists_normal_index l hH
end ReciprocityTheory.DiscreteGroups.LocalClassField
