-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.quadraticDifferenceArith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:19.726432+00:00
-- url     : https://prove2.me/submissions/65098944-5b1f-4c98-b09e-5c735fedcc9c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_arith_real
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_prod
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_pos
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_pow
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_alp_ne_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_natCast_ne_zero


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
open scoped Classical
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution : Arith (F := F) v := by
  intro typed g r m ht hg
  unfold jacS
  simp only [if_pos ht, absV_mul, absV_prod, absV_pow, absV_inv]
  exact arith_real r _ (fun i => absV_pos v (alp_ne_zero v r i)) _ m
    (absV_pos v (natCast_ne_zero v hg))
end PI.UnitaryGroupMassFormula.LocJacTyp
