-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:55.140036+00:00
-- url     : https://prove2.me/submissions/9a42713b-dca4-40b8-b1e0-0dc1c2fb33be

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfMemBrKerOfCoprime
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_BrKer_iff
import Theorems.Thm_ReciprocityTheory_Coh_cor_holds
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finiteIndex_subG
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isOpen_subG


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
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K) (hx : x ∈ BrKer h) :
    degLK p K L • x = 0 := by
  have := finiteIndex_subG (K := K) hL
  obtain ⟨cor, -, hcor⟩ := cor_holds ℤ (GK p K) (kbarT p K) (subG p K L) (isOpen_subG hL)
  have h2 := hcor 2 x
  rw [(mem_BrKer_iff h x).1 hx, map_zero] at h2
  exact h2.symm
end ReciprocityTheory.DiscreteGroups.LocalClassField
