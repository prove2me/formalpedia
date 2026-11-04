-- Prove2me | solution 1 for ThreeSum.PolynomialResources.polyBound_of_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:48.846203+00:00
-- url     : https://prove2.me/submissions/525999f8-ed44-4922-9c9b-b9e0b8bdc08d

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Theorems.Thm_ThreeSum_PolynomialResources_natural_polynomial_of_powerBound
import Theorems.Thm_Light_le_polyBound_of_le_pow
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
    ∃ s k : ℕ, ∀ n : ℕ, f n ≤ Light.polyBound s k [n] := by
  obtain ⟨C,k,h⟩ := natural_polynomial_of_powerBound hf
  exact ⟨Nat.size C,k,fun n => by
    simpa only [zero_add] using Light.le_polyBound_of_le_pow (s := 0) le_rfl (h n)⟩
end ThreeSum.PolynomialResources
