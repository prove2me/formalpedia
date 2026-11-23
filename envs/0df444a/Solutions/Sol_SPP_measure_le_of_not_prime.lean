-- Prove2me | solution 1 for SPP.measure_le_of_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:31:24.717054+00:00
-- url     : https://prove2.me/submissions/d572f6ab-6cd5-4e0b-9b35-17eeb3608fe6

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_card_le_of_not_prime
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
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SPP
theorem _root_.solution {n : ℕ} [hn : Fact (1 < n)] (ho : Odd n) (hnp : ¬n.Prime) :
    (millerRabinRandomSource n).toMeasure {a | SPP n a} ≤ 1 / 4 := by
  calc
    _ = #{a | SPP n a} / (n - 1 : ℝ≥0∞) := by
      erw [PMF.toMeasure_uniformOfFinset_apply (ht := by measurability),
        Finset.filter_congr_decidable]
      have h : ({a ≠ 0 | SPP n a} : Finset _) = ({a | SPP n a} : Finset _) := by
        ext a
        suffices SPP n a → a ≠ 0 by simpa
        rintro h rfl
        exact not_spp_zero n h
      simp [Finset.card_compl, h]
    _ = (4 * #{a | SPP n a}) / (n - 1) / 4 := by
      rw [mul_div_assoc, mul_comm 4, ENNReal.mul_div_cancel_right] <;> norm_num
    _ ≤ (n - 1) / (n - 1) / 4 := by
      gcongr
      norm_cast
      exact card_le_of_not_prime ho hnp
    _ = 1 / 4 := by
      rw [ENNReal.div_self]
      · norm_cast; have := hn.out; omega
      · simp
end SPP
