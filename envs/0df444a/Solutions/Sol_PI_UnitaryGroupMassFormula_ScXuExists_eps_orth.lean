-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.eps_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:52:43.514712+00:00
-- url     : https://prove2.me/submissions/f804ceb0-d583-44dd-9e27-3efd9964cbcf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_psiV_sigR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) :
    PI.FinKW.psiV I v Rf.ew * PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) = 0 := by
  rw [← PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR, ← map_mul]
  have h := Rf.ew_orth
  have h' : Rf.ew * Formalism.UG.sigR I.cm.sig (Af I.F) Rf.ew = 0 := h
  rw [h', map_zero]
end PI.UnitaryGroupMassFormula.ScXuExists
