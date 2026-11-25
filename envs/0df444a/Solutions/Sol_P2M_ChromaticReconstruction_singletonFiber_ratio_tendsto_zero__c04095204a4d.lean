-- Prove2me | solution 1 for P2M_ChromaticReconstruction_singletonFiber_ratio_tendsto_zero__c04095204a4d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:13:08.829015+00:00
-- url     : https://prove2.me/submissions/b8b719de-cbee-4447-b88c-0303c94eea48

import Definitions.Def_RequestProject_CountingUpper
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_CountingLimit
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_singletonFiberCount_le
import Theorems.Thm_ChromaticReconstruction_two_pow_le_card_treeClass
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr



set_option autoImplicit true
open Filter Topology
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (t : ℕ) :
    Tendsto (fun k => (singletonFiberCount k t : ℝ) / Nat.card (TreeClass k)) atTop (𝓝 0) := by
  set C := (t + 1) ^ (t + 2) with hC
  set D := 2 * t * C with hD
  let h : ℕ → ℝ := fun k =>
    (8 * 2 ^ C : ℝ) * (((Nat.sqrt k + 1 : ℕ) : ℝ) ^ D / 2 ^ (Nat.sqrt k + 1))
  have hs : Tendsto (fun k => Nat.sqrt k + 1) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b * b, fun k hk => ?_⟩
    have := Nat.le_sqrt.2 hk
    omega
  have hh : Tendsto h atTop (𝓝 0) := by
    have := ((tendsto_pow_const_div_const_pow_of_one_lt D (one_lt_two : (1 : ℝ) < 2)).comp
      hs).const_mul (8 * 2 ^ C : ℝ)
    rw [mul_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh ?_ ?_
  · exact Eventually.of_forall fun k => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 3] with k hk
    set s := Nat.sqrt k with hsdef
    have hN : (2 : ℝ) ^ (s - 2) ≤ Nat.card (TreeClass k) := by
      exact_mod_cast two_pow_le_card_treeClass hk
    have hU : (singletonFiberCount k t : ℝ) ≤ ((2 ^ C * (s + 1) ^ D : ℕ) : ℝ) := by
      have h1 := singletonFiberCount_le k t
      have h2 : k ^ t + 1 ≤ 2 * (s + 1) ^ (2 * t) := by
        have hk1 : k < (s + 1) ^ 2 := Nat.lt_succ_sqrt' k
        have h3 : k ^ t ≤ ((s + 1) ^ 2) ^ t := Nat.pow_le_pow_left hk1.le t
        have h4 : 1 ≤ k ^ t := Nat.one_le_pow _ _ (by omega)
        rw [← pow_mul] at h3
        omega
      have h3 : (k ^ t + 1) ^ C ≤ 2 ^ C * (s + 1) ^ D := by
        calc (k ^ t + 1) ^ C ≤ (2 * (s + 1) ^ (2 * t)) ^ C := Nat.pow_le_pow_left h2 C
          _ = 2 ^ C * (s + 1) ^ D := by rw [mul_pow, ← pow_mul]
      exact_mod_cast h1.trans h3
    have hpos : (0 : ℝ) < 2 ^ (s - 2) := by positivity
    calc (singletonFiberCount k t : ℝ) / Nat.card (TreeClass k)
        ≤ ((2 ^ C * (s + 1) ^ D : ℕ) : ℝ) / 2 ^ (s - 2) :=
          div_le_div₀ (by positivity) hU hpos hN
      _ ≤ h k := by
          have h8 : (2 : ℝ) ^ (s + 1) ≤ 8 * 2 ^ (s - 2) := by
            have : s + 1 ≤ 3 + (s - 2) := by omega
            calc (2 : ℝ) ^ (s + 1) ≤ 2 ^ (3 + (s - 2)) := pow_le_pow_right₀ (by norm_num) this
              _ = 8 * 2 ^ (s - 2) := by rw [pow_add]; norm_num
          simp only [h]
          push_cast
          rw [mul_div_assoc', div_le_div_iff₀ hpos (by positivity)]
          have hX : (0 : ℝ) ≤ 2 ^ C * ((s : ℝ) + 1) ^ D := by positivity
          calc 2 ^ C * ((s : ℝ) + 1) ^ D * 2 ^ (s + 1)
              ≤ 2 ^ C * ((s : ℝ) + 1) ^ D * (8 * 2 ^ (s - 2)) :=
                mul_le_mul_of_nonneg_left h8 hX
            _ = 8 * 2 ^ C * ((s : ℝ) + 1) ^ D * 2 ^ (s - 2) := by ring
end ChromaticReconstruction
