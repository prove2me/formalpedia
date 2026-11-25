-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.matV_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:29.802012+00:00
-- url     : https://prove2.me/submissions/5e7cf8cc-0cba-4951-ab22-b191cfa2f461

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y x : I.Gf) :
    matV I v ((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) =
      (matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)))⁻¹ * matV I v (x : GL (Fin I.n) _) := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
end PI.UnitaryGroupMassFormula.AdIndexEq
