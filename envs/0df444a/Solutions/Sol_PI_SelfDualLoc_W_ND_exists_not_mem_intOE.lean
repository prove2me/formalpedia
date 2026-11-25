-- Prove2me | solution 1 for PI.SelfDualLoc.W.ND.exists_not_mem_intOE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:21.002045+00:00
-- url     : https://prove2.me/submissions/ea880385-28dd-46d9-93d4-2fb7bb8a4e6a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
import Theorems.Thm_PI_SelfDualLoc_W_ND_mem_intOE_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W PI.SelfDualLoc.W.ND
open PI.SelfDualLoc
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.SelfDualLoc.W.ND
theorem _root_.solution : ∃ t : E, t ∉ intOE E := by
  refine ⟨(2 : E)⁻¹, fun h => ?_⟩
  obtain ⟨a, ha⟩ := (mem_intOE_iff _).1 h
  have h1 : IsIntegral ℤ ((2 : E)⁻¹) := ha ▸ RingOfIntegers.isIntegral_coe a
  have h2 : algebraMap ℚ E ((2 : ℚ)⁻¹) = (2 : E)⁻¹ := by simp
  rw [← h2] at h1
  have h3 : IsIntegral ℤ ((2 : ℚ)⁻¹) := (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 h1
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (2 : ℚ) * (z : ℚ) = 1 := by
    rw [show (z : ℚ) = (2 : ℚ)⁻¹ by simpa using hz]
    norm_num
  have h5 : (2 : ℤ) * z = 1 := by exact_mod_cast h4
  omega
end PI.SelfDualLoc.W.ND
