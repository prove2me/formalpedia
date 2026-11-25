-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.eps_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:15.598652+00:00
-- url     : https://prove2.me/submissions/92ca6c60-9c52-49ac-9e00-3e225ff9d202

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul

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
    PI.FinKW.psiV I v Rf.ew * PI.FinKW.psiV I v Rf.ew = PI.FinKW.psiV I v Rf.ew := by
  rw [← map_mul, Rf.ew_idem]
end PI.UnitaryGroupMassFormula.ScXuExists
