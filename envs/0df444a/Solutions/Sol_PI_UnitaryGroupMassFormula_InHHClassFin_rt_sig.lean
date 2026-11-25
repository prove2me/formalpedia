-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.rt_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:25.413066+00:00
-- url     : https://prove2.me/submissions/c0b0f4bd-03a5-475f-bb9b-5dc6c6f43655

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_RtUnitaryOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (e : I.E) :
    sigR I.cm.sig (FiniteAdeleRing (𝓞 I.F) I.F) (rtι I e) = rtι I (starRingEnd I.E e) := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F _) (e ⊗ₜ 1) = (starRingEnd I.E e) ⊗ₜ 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl
end PI.UnitaryGroupMassFormula.InHHClassFin
