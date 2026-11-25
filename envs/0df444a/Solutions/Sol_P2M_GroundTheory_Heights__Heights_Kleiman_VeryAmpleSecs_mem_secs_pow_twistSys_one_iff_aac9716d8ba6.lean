-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_secs_pow_twistSys_one_iff_aac9716d8ba6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:19.185879+00:00
-- url     : https://prove2.me/submissions/8c0e65b7-62a5-485a-b0ee-ef9d5d72700a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSecs
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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
theorem _root_.solution {r : ℕ} (h : Fin (r + 1) → Ω) (n : ℕ) (s : Ω) :
    s ∈ ((twistSys k h 1).pow n).secs ↔ ∀ j, h j ≠ 0 → s / h j ^ n ∈ ampleBase (S := k) h j := by
  constructor
  · intro hs j hj
    have hsj := (Submodule.mem_iInf _).mp hs (singleChart hj)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (pow_twistSys_one_le n (singleChart hj) (Finset.mem_singleton_self j) hsj)
    rw [chartRing_smul_def] at hb
    rw [← hb, mul_div_cancel_right₀ _ (pow_ne_zero n hj)]
    exact mem_ampleBase_of_mem_chartRing hj b.2
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hhi : h i ≠ 0 := (mem_support h).mp (I.2.2 hi)
    have hbase : ampleBase (S := k) h i ≤ chartRing k h (singleChart hhi) := by
      rw [ampleBase, Algebra.adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      exact (ratio (S := k) hhi l).2
    have hmem : s / h i ^ n ∈ chartRing k h I :=
      chartRing_mono (Finset.singleton_subset_iff.mpr hi) (hbase (H i hhi))
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    have hs : s = (⟨s / h i ^ n, hmem⟩ : chartRing k h I) • h i ^ n := by
      rw [chartRing_smul_def, div_mul_cancel₀ _ (pow_ne_zero n hhi)]
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ (mem_twistMod_one I i) n)
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
