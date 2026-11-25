-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.Hpk_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:00:34.504102+00:00
-- url     : https://prove2.me/submissions/35c8ab21-2053-4d60-9385-2367ff4b7e55

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_Hpk_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_sig_sig
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_sgn_sig
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_sgn_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FibOrbAsmW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
namespace PI.UnitaryGroupMassFormula.FibOrbAsmW
theorem _root_.solution (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [mul_apply, Finset.sum_eq_single (sig k r i)]
  · rw [Hpk_apply, Hpk_apply, if_pos rfl, sig_sig, sgn_sig, one_apply]
    by_cases h : j = i
    · subst h; rw [if_pos rfl, if_pos rfl, sgn_mul_self]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro l _ hl
    rw [Hpk_apply, if_neg hl, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.UnitaryGroupMassFormula.FibOrbAsmW
