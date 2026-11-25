-- Prove2me | solution 1 for PI.WGL.lm_last_of_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:04.10978+00:00
-- url     : https://prove2.me/submissions/37b97350-4a1c-48d6-b845-f27572e9b3be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {N : ℕ} (hN : 0 < N) (f : MvPolynomial (Fin N × Fin N) ℂ) (ω : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f ω) :
    IsWeightedHomogeneous (lastW N) f (ω ⟨N - 1, by omega⟩) := by
  intro m hm
  rw [← hf hm, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [lastW, rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Fin.ext_iff]
  by_cases hv : v.1.1 + 1 = N
  · rw [if_pos hv, if_pos (by omega)]
  · rw [if_neg hv, if_neg (by omega)]
end PI.WGL
