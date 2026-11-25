-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_Parabolic_exists_blockUpper_mul_integralGL__7c8211cc1088
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:36.959851+00:00
-- url     : https://prove2.me/submissions/26b9f3b2-8f9a-4e1b-b656-8e430856f12a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_permuteGL_mem_integralGL_iff
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_permuteGL_mem_blockUpper_iff
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_exists_blockUpper_mul_integralGL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (g : GL (Fin n) F) :
    ∃ p ∈ blockUpper F n β, ∃ k ∈ integralGL F n, g = p * k := by
  set s : Equiv.Perm (Fin n) := Tuple.sort β
  have hs : Monotone (β ∘ s) := Tuple.monotone_sort β
  obtain ⟨p, hp, k, hk, hpk⟩ :=
    exists_blockUpper_mul_integralGL F n hs ((permuteGL F s).symm g)
  refine ⟨permuteGL F s p, (permuteGL_mem_blockUpper_iff s).2 hp, permuteGL F s k,
    (permuteGL_mem_integralGL_iff s).2 hk, ?_⟩
  rw [← map_mul, ← hpk, MulEquiv.apply_symm_apply]
end GroundTheory.Automorphic.Parabolic
