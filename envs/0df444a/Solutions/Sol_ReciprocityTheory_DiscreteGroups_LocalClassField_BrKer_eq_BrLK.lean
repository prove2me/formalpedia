-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.BrKer_eq_BrLK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:56.972095+00:00
-- url     : https://prove2.me/submissions/d8a84957-aab0-4d7a-a205-18e612cd4ef3

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfMemBrKerOfCoprime
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_BrKer_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_invariants_isInvRep
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_infRes2_exact
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isOpen_subG
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_restricted_multiplicative_h1_subsingleton


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
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] :
    BrKer h = BrLK p K L := by
  ext x
  rw [mem_BrKer_iff]
  exact infRes2_exact (kbarT p K) (subG p K L) (isOpen_subG hL) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)
    (restricted_multiplicative_h1_subsingleton p K _) x
end ReciprocityTheory.DiscreteGroups.LocalClassField
