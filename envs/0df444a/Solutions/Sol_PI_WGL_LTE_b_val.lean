-- Prove2me | solution 1 for PI.WGL.LTE.b_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:29.396017+00:00
-- url     : https://prove2.me/submissions/4159c4c7-53ca-4945-8569-71720071cc44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
namespace PI.WGL.LTE
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : ℕ) (ht : t < n) :
    (((bb h lam sg ⟨t, ht⟩).toNat : ℕ) : ℤ) = lam.w ⟨t, by omega⟩ - sg.w ⟨t, ht⟩ := by
  have h1 := (hI ⟨t, ht⟩).1
  have e : lam.w ⟨(⟨t, ht⟩ : Fin n).1, by omega⟩ = lam.w ⟨t, by omega⟩ := rfl
  unfold bb
  omega
end PI.WGL.LTE
