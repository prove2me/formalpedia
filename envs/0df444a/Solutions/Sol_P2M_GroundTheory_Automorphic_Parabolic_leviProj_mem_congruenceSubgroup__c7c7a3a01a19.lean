-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_Parabolic_leviProj_mem_congruenceSubgroup__c7c7a3a01a19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:55.562131+00:00
-- url     : https://prove2.me/submissions/5055d3b1-e730-4f64-b5da-8a3bc18c1df8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_leviProj
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {α : Type*} [LinearOrder α] {β : Fin n → α}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {j : ℕ} {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ congruenceSubgroup F n j) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) ∈ congruenceSubgroup F n j := by
  rw [mem_congruenceSubgroup_iff] at hp ⊢
  obtain ⟨hint, hcong⟩ := hp
  refine ⟨?_, fun i k => ?_⟩
  · rw [mem_integralGL_iff F n] at hint ⊢
    refine ⟨fun i k => ?_, fun i k => ?_⟩
    · rw [leviProj_apply]
      split_ifs
      · exact hint.1 i k
      · exact zero_mem _
    · have : ((leviProj F n β p : levi F n β) : GL (Fin n) F)⁻¹ =
          ((leviProj F n β p⁻¹ : levi F n β) : GL (Fin n) F) := by
        rw [map_inv]
        rfl
      rw [this, leviProj_apply]
      split_ifs
      · exact hint.2 i k
      · exact zero_mem _
  · rw [leviProj_apply]
    split_ifs with h
    · exact hcong i k
    · have hik : i ≠ k := fun e => h (e ▸ rfl)
      rw [Matrix.one_apply_ne hik, sub_zero, map_zero]
      exact zero_le
end GroundTheory.Automorphic.Parabolic
