-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_index_ne_zero_0c8323a65fb2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:46.917829+00:00
-- url     : https://prove2.me/submissions/059db6ec-640d-4a78-a24a-426d1d3e509f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_int_eq_mul_1252f130419c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_index_ne_zero_of_zsmul_mem_ed4642d5576e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
theorem _root_.solution [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {I : Ideal B} (hI : I ≠ ⊥) :
    I.toAddSubgroup.index ≠ 0 := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨c, hc, q, hq⟩ := OrderIdealIndexExtensionAlt.exists_int_eq_mul ha
  refine OrderIdealIndexExtensionAlt.index_ne_zero_of_zsmul_mem _ hc fun x => ?_
  have e : c • x = a * (q * x) := by rw [zsmul_eq_mul, hq, mul_assoc]
  rw [Submodule.mem_toAddSubgroup, e]
  exact I.mul_mem_right _ haI
end GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
