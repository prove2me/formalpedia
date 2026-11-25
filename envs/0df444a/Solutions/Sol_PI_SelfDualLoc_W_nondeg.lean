-- Prove2me | solution 1 for PI.SelfDualLoc.W.nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:28.598098+00:00
-- url     : https://prove2.me/submissions/8a8f06da-72b6-4848-8664-fc79a2ad7c2c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
import Theorems.Thm_PI_SelfDualLoc_W_ND_exists_den
import Theorems.Thm_PI_SelfDualLoc_W_ND_exists_not_mem_intOE
import Theorems.Thm_PI_SelfDualLoc_W_ND_hform_smul_right

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
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc ND
namespace PI.SelfDualLoc.W
theorem _root_.solution : Nondeg := by
  intro F E _ _ _ _ _ n σ J Lb T hfin hT hT0 y hy
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨d, hd0, hd⟩ := exists_den Lb (Module.Finite.iff_fg.1 hfin)
  obtain ⟨t, ht⟩ := exists_not_mem_intOE (E := E)
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hT' : (T : E) ≠ 0 := by exact_mod_cast hT0
  have hmem : (T : E) • ((t / ((d : E) * (T : E) * y j)) • y) ∈ Lb := by
    apply hT
    intro x hx
    rw [hform_smul_right, hy x hx, mul_zero]
    exact zero_mem _
  have := hd _ hmem j
  apply ht
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
end PI.SelfDualLoc.W
