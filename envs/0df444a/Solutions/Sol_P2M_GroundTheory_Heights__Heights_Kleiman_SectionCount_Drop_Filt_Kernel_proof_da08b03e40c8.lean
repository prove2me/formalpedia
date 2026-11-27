-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_proof_da08b03e40c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:34.058925+00:00
-- url     : https://prove2.me/submissions/ef8abb26-05e7-41b1-83f7-4f3ccf9c7bde

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltKernelSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropFiltKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_mem_secs_iff__29664b360f03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_idealMod_le_e980b8caa17f

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
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel
theorem _root_.solution : SectionCount.Drop.Filt.Kernel.Statement.{u, w} := by
  intro S _ Ω _ _ N x j b F hj
  have hjb : x j ^ b ≠ 0 := pow_ne_zero _ hj
  constructor
  · intro t ht
    refine mem_secs_iff'.mpr fun I => ?_
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp ht I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · change q ∈ twistMod S x (-(b : ℤ)) I at hq
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      have h := (F.sub I).smul_mem (a * ratioPow I hi j b) hy
      rw [chartRing_smul_def] at h ⊢
      convert h using 1
      simp only [ratioPow, Subalgebra.coe_mul, zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact (F.sub I).add_mem hu hv
  · intro s hs
    refine ⟨(x j ^ b)⁻¹ * s, mem_secs_iff'.mpr fun I => ?_, by field_simp⟩
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp hs I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    rw [SubSystem.twist_sub_eq_mul_of_line]
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (idealMod_le j b I hi hq)
      have hq' : (a : Ω) * x i ^ (-(b : ℤ)) ∈ (twistSys S x (-(b : ℤ))).sub I := by
        change _ ∈ twistMod S x (-(b : ℤ)) I
        rw [twistMod_eq_span _ I hi]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
      convert Submodule.mul_mem_mul hq' hy using 1
      rw [chartRing_smul_def]
      simp only [zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact add_mem hu hv
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel
