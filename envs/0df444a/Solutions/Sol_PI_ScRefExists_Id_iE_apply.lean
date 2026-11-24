-- Prove2me | solution 1 for PI.ScRefExists.Id.iE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:43.263844+00:00
-- url     : https://prove2.me/submissions/387aca75-1b7d-4b30-85c2-99cb4fdf57f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemTen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.Id
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.Id
theorem _root_.solution (e : I.E) : iE I e = e ⊗ₜ[I.F] (1 : Af I.F) :=
  Algebra.TensorProduct.includeLeftRingHom_apply e
end PI.ScRefExists.Id
