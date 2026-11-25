-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.Gl.vec_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:43:48.792681+00:00
-- url     : https://prove2.me/submissions/a512aa6d-2440-4ef4-939e-20e0d481ae2e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Theorems.Thm_PI_FinKW_local_vector_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.Gl
theorem _root_.solution (I : AutInst) (x y : Fin I.n → I.E ⊗[I.F] Af I.F)
    (h : ∀ v, PI.FinKW.vecV I v x = PI.FinKW.vecV I v y) : x = y := by
  funext i
  have h0 : x i - y i = 0 := PI.FinKW.local_vector_injective I (x i - y i) (fun v => by
    rw [map_sub]
    exact sub_eq_zero.2 (congrFun (h v) i))
  exact sub_eq_zero.1 h0
end PI.UnitaryGroupMassFormula.ScXuExists.Gl
