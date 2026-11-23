-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_closure_commutator_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:45.849657+00:00
-- url     : https://prove2.me/submissions/4b6274b5-dc02-4384-a428-27814f4d49a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_subG_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isClosed_subG
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti


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
open Topology
open scoped commutatorElement
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) (g : GK p K) :
    g ∈ (commutator (GK p K)).topologicalClosure ↔ ∀ L, IsAbLK p K L → g ∈ subG p K L := by
  constructor
  · intro hg L hL
    exact Subgroup.topologicalClosure_minimal _ hL.comm (isClosed_subG p K L) hg
  · intro hg
    obtain ⟨M, hM, hMe⟩ := exists_subG_eq (commutator (GK p K)).topologicalClosure
      (Subgroup.isClosed_topologicalClosure _)
    rw [← hMe]
    intro x hx
    have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
    have hfd : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hle : K ⊔ IntermediateField.adjoin ℚ_[p] {x} ≤ M :=
      sup_le hM (IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hx))
    have hab : IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {x}) := by
      refine ⟨le_sup_left, IntermediateField.finiteDimensional_sup _ _, ?_⟩
      refine le_trans ?_ (subG_anti hle)
      rw [hMe]
      exact Subgroup.le_topologicalClosure _
    exact hg _ hab x (le_sup_right (a := K) (IntermediateField.mem_adjoin_simple_self ℚ_[p] x))
end ReciprocityTheory.DiscreteGroups.LocalClassField
