-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:20.88914+00:00
-- url     : https://prove2.me/submissions/b5fa5dd9-3da6-40c1-ae75-b48663331f4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_one

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => simp [absV_one]
  | succ n ih => rw [pow_succ, absV_mul, ih, pow_succ]
end PI.UnitaryGroupMassFormula.LocJacTyp
