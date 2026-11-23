-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.not_dvd_qK_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:03.733955+00:00
-- url     : https://prove2.me/submissions/274c8d8c-812d-4ab4-ad54-7ac6679ee7b9

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_eq_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {n : ℕ} (hn : 0 < n) : ¬ p ∣ qK p K ^ n - 1 := by
  obtain ⟨f, hf, h⟩ := qK_eq_pow K hK
  intro hd
  have h1 : p ∣ qK p K ^ n := by
    rw [h, ← pow_mul]; exact dvd_pow_self p (Nat.mul_pos hf hn).ne'
  have h2 : 1 ≤ qK p K ^ n := Nat.one_le_pow _ _ (by have := one_lt_qK K hK; omega)
  have h3 : p ∣ 1 := by
    have := (Nat.dvd_sub h1 hd)
    rwa [Nat.sub_sub_self h2] at this
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
