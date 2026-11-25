-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.sigV_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:34.771223+00:00
-- url     : https://prove2.me/submissions/7c70a687-1054-4e05-8ff2-f2b3451ae29d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_sigV_tmul

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
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : sigV I v (sigV I v a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x e => rw [sigV_tmul, sigV_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end PI.UnitaryGroupMassFormula.AdIndexEq
