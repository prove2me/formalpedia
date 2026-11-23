-- Prove2me | solution 1 for SPP.card_le_of_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:28:17.248803+00:00
-- url     : https://prove2.me/submissions/7d2e36e3-ef89-4d50-b7ef-b1945d7ae05f

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_isUnit
import Theorems.Thm_SPP_mem_nonwitnessGroup
import Theorems.Thm_SPP_card_nonwitnessGroup_le_of_not_prime
import Theorems.Thm_FPP_isUnit
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
attribute [local simp] P2M_ZMod_fst_chineseRemainder__e38dff19d888
attribute [local simp] P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] Subgroup.mem_closure_neg_one
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder
attribute [local simp] ZMod.unitsMap_neg



set_option autoImplicit false
open Nat
open SPP
open Finset
namespace SPP
theorem _root_.solution {n : ℕ} [hn : Fact (1 < n)] (ho : Odd n) (hnp : ¬n.Prime) :
    4 * #{a | SPP n a} ≤ n - 1 := by
  rcases eq_or_ne n 9 with rfl | h9
  · have val28 : val₂ 8 = 3 := padicValNat.prime_pow 3
    have (a : ZMod 9) : SPP 9 a ↔ a = 1 ∨ a = -1 := by
      rw [SPP, oddPart, val28]
      constructor
      · contrapose!
        intro ⟨h1, hn1⟩
        fin_cases a <;> first | contradiction | decide
      · rintro (rfl | rfl) <;> decide
    simp_rw [this]
    decide +revert
  · calc
      _ = 4 * Nat.card {a // SPP n a} := by simp [Fintype.card_subtype]
      _ ≤ 4 * Nat.card (nonwitnessGroup n) := by
        gcongr
        have (x : {a // SPP n a}) : ∃ a' : nonwitnessGroup n, a'.val.val = x.val := by
          choose a' ha' using x.prop.isUnit
          use ⟨a', mem_nonwitnessGroup (ha' ▸ x.prop)⟩
        choose f hf using this
        apply Nat.card_le_card_of_injective f
        intro ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h
        simpa [hf] using congr(($h).val.val)
      _ ≤ φ n := card_nonwitnessGroup_le_of_not_prime ho hnp h9
      _ ≤ n - 1 := le_pred_of_lt (totient_lt n hn.out)
end SPP
