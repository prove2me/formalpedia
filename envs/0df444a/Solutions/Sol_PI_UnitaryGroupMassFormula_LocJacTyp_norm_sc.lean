-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.norm_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:53.711938+00:00
-- url     : https://prove2.me/submissions/4bc708b4-d4a6-4da4-a027-76fa561a9f0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitScale

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (hfin : Module.finrank F E = 2) (x : Fv F v) :
    Algebra.norm (Fv F v) (sc (E := E) v x) = x ^ 2 := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have h1 : sc (E := E) v x = algebraMap (Fv F v) (Fv F v ⊗[F] E) x := by
    simp [PI.LocJacTyp.sc, Algebra.TensorProduct.algebraMap_apply]
  rw [h1, Algebra.norm_algebraMap, Module.finrank_baseChange, hfin]
end PI.UnitaryGroupMassFormula.LocJacTyp
