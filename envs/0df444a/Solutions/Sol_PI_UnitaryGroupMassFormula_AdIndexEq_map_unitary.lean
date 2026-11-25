-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.map_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:23.451619+00:00
-- url     : https://prove2.me/submissions/f2840fa7-b80d-47bd-804c-e29dc17ea73d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_psiV_sigR
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_map_cT
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mapJ

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
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) M * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * M).map
              (PI.FinKW.psiV I v).toRingHom =
      Formalism.UG.cT (sigV I v) (M.map (PI.FinKW.psiV I v).toRingHom) * I.J.map (inclV I v) *
        M.map (PI.FinKW.psiV I v).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul,
    map_cT (PI.FinKW.psiV I v).toRingHom (Formalism.UG.sigR I.cm.sig (Af I.F)) (sigV I v)
      (fun a => psiV_sigR I v a), mapJ]
end PI.UnitaryGroupMassFormula.AdIndexEq
