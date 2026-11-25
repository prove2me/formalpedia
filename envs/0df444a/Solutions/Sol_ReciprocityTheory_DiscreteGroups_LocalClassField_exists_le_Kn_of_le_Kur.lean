-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_le_Kn_of_le_Kur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:41.477306+00:00
-- url     : https://prove2.me/submissions/ba76dfdc-3f1f-4785-a5cd-b81deba08195

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kur_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kn_mono
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_mono


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
variable {p K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {M : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (h : M ≤ MaximalUnramifiedExtension p K) : ∃ n, 0 < n ∧ M ≤ Kn p K n := by
  let b := Module.finBasis ℚ_[p] M
  have h1 : ∀ i, ∃ n, 0 < n ∧ (b i : PadicAlgCl p) ∈ Kn p K n := fun i => (mem_Kur_iff hK _).1 (h (b i).2)
  choose N hN hb using h1
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun x hx => ?_⟩
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p) := by
    have := congrArg M.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    exact this.symm
  rw [hx']
  refine sum_mem fun i _ => ?_
  exact (Kn p K (∏ i, N i)).smul_mem (Kn_mono p K hK (Finset.dvd_prod_of_mem N (Finset.mem_univ i)) (hb i))
end ReciprocityTheory.DiscreteGroups.LocalClassField
