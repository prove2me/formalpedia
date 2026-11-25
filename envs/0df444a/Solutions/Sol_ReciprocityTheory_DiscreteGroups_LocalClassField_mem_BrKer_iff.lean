-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_BrKer_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:36.482271+00:00
-- url     : https://prove2.me/submissions/18c9dd30-5aa7-463a-8bbd-fa94fa995e3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfMemBrKerOfCoprime
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_resPair_factor


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
theorem _root_.solution (h : K ≤ L) (x : Br p K) :
    x ∈ BrKer h ↔ (resP (kbarT p K) (subG p K L)).hom.H 2 x = 0 := by
  obtain ⟨e, he, hf⟩ := exists_resPair_factor h
  show (resPair h).hom.H 2 x = 0 ↔ _
  rw [hf 2 x]
  exact map_eq_zero_iff _ (he 2).1
end ReciprocityTheory.DiscreteGroups.LocalClassField
