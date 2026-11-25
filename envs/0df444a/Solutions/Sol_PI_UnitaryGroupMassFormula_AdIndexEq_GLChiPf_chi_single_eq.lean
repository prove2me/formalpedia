-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.chi_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:19.173382+00:00
-- url     : https://prove2.me/submissions/c62176fb-a355-4b0e-80da-bc71984ded64

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_chi_conj
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_sU_conj_dU
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_mulSingle_comp_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
theorem _root_.solution (χ : GL (Fin n) k →* ℚ) (i j : Fin n) (d : kˣ) :
    χ (dU (Pi.mulSingle i d)) = χ (dU (Pi.mulSingle j d)) := by
  have h := chi_conj χ (sU (Equiv.swap i j) (Equiv.symm_swap i j)) (dU (Pi.mulSingle i d))
  rw [sU_conj_dU, mulSingle_comp_swap] at h
  exact h.symm
end PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
