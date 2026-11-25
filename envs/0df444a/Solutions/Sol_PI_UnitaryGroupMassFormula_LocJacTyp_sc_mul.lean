-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.sc_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:13.637138+00:00
-- url     : https://prove2.me/submissions/39adc2f6-c4ce-497a-87d5-3542fa06518b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Theorems.Thm_PI_VolStabSW_HasDens_add
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (t : Fv F v) (x : Fv F v ⊗[F] E) : sc (E := E) v t * x = t • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [mul_add, smul_add, hx, hy]
end PI.UnitaryGroupMassFormula.LocJacTyp
