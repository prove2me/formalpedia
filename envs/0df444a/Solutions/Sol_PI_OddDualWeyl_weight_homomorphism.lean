-- Prove2me | solution 1 for PI.OddDualWeyl.weight_homomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:13.013784+00:00
-- url     : https://prove2.me/submissions/c4a58bff-6d73-4997-b1a0-49edbad6ca2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_applyWord_tot
import Theorems.Thm_PI_OddDualWeyl_Hom_hw_tot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open Hom
namespace PI.OddDualWeyl
theorem _root_.solution : HomW := by
  intro R _ k ν f hf
  have hle : weyl R k k (le_refl k) ν ≤ homogeneousSubmodule (Fin k × Fin k) R (degW ν) := by
    rw [weyl, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    exact applyWord_tot w (hw_tot ν)
  have := hle hf
  rwa [mem_homogeneousSubmodule] at this
end PI.OddDualWeyl
