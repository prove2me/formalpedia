-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_proof_ecd492e14d28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:36.296047+00:00
-- url     : https://prove2.me/submissions/397589f3-86b8-4cac-ad3d-05d104d7214a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSecs
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_secs_pow_twistSys_one_iff_aac9716d8ba6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_pow_of_pow_mul_mem_f7465f8a4c1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_exists_pow_mul_mem_pow_84ca433e9bcd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open VeryAmpleSecs
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleSecs
theorem _root_.solution : VeryAmpleSecs.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb r h hv n
  ext s
  rw [mem_secs_pow_twistSys_one_iff]
  have hL : ∀ I l, h l ∈ Nb.sub I := fun I l => (Submodule.mem_iInf _).mp (hv.mem_secs l) I
  constructor
  · intro hs j hj
    refine hv.closed j hj (Set.mem_iInter.mpr fun I => ⟨n, ?_⟩)
    rw [div_mul_cancel₀ _ (pow_ne_zero n hj), one_mul]
    exact (Submodule.mem_iInf _).mp hs I
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    obtain ⟨Q, hQ⟩ := Nb.invertible I
    refine mem_pow_of_pow_mul_mem hQ (hv.generates I) fun j => ?_
    by_cases hj : h j = 0
    · exact ⟨1, by rw [hj, pow_one, zero_mul]; exact Submodule.zero_mem _⟩
    obtain ⟨e, he⟩ := exists_pow_mul_mem_pow (hL I) hj (H j hj)
    refine ⟨e, ?_⟩
    have hs : h j ^ e * s = h j ^ n * (h j ^ e * (s / h j ^ n)) := by
      field_simp
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL I j) n) he
end VeryAmpleSecs
end GroundTheory.Heights₂.Heights.Kleiman
