-- Prove2me | solution 1 for ThreeSum.PolynomialResources.pair_polyBound_of_powerBound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:44.707521+00:00
-- url     : https://prove2.me/submissions/b7b338ba-d8b8-4527-abd2-a7e75cf10862

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Theorems.Thm_ThreeSum_PolynomialResources_polyBound_of_powerBound
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
theorem _root_.solution {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (e : ℕ) :
    ∃ s k : ℕ, ∀ n U : ℕ, f n*(U+1)^e ≤ Light.polyBound s k [n,U] := by
  obtain ⟨s,k,h⟩ := polyBound_of_powerBound hf
  refine ⟨s,k+e,fun n U => ?_⟩
  have hn : (n+1)^k ≤ (n+1)^(k+e) := Nat.pow_le_pow_right (by omega) (by omega)
  have hU : (U+1)^e ≤ (U+1)^(k+e) := Nat.pow_le_pow_right (by omega) (by omega)
  have hf' : f n ≤ 2^s*(n+1)^k := by simpa only [Light.polyBound,List.map_cons,
    List.map_nil,List.prod_cons,List.prod_nil,mul_one] using h n
  calc
    _ ≤ (2^s*(n+1)^k)*(U+1)^e := Nat.mul_le_mul_right _ hf'
    _ ≤ (2^s*(n+1)^(k+e))*(U+1)^(k+e) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) hU
    _ = Light.polyBound s (k+e) [n,U] := by simp [Light.polyBound,mul_pow,mul_assoc]
end ThreeSum.PolynomialResources
