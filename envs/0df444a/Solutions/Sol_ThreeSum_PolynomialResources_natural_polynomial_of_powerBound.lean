-- Prove2me | solution 1 for ThreeSum.PolynomialResources.natural_polynomial_of_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:29.372063+00:00
-- url     : https://prove2.me/submissions/414779ae-d61e-4339-879d-e5a446bcfb53

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.PolynomialResources
open StageBounds Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.PolynomialResources
theorem _root_.solution {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    ∃ C k : ℕ, ∀ n : ℕ, f n ≤ C*(n+1)^k := by
  let k : ℕ := ⌈a+1⌉₊
  have hk : a+1 ≤ (k : ℝ) := Nat.le_ceil _
  have he : ∀ᶠ n : ℕ in atTop, f n ≤ n^k := by
    filter_upwards [hf 1 (by norm_num),eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hh := hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hk)
    rw [Real.rpow_natCast] at hh
    exact_mod_cast hh
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  let C : ℕ := 1+∑ i ∈ Finset.range N, f i
  have hC : 1 ≤ C := by dsimp [C]; omega
  refine ⟨C,k,fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact ((hN n hn).trans (Nat.pow_le_pow_left (by omega) k)).trans
      (Nat.le_mul_of_pos_left _ hC)
  · have hh : f n ≤ ∑ i ∈ Finset.range N, f i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have hsmall : f n ≤ C := by dsimp [C]; omega
    exact hsmall.trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))
end ThreeSum.PolynomialResources
