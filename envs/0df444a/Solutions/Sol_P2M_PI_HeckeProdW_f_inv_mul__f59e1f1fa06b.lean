-- Prove2me | solution 1 for P2M_PI_HeckeProdW_f_inv_mul__f59e1f1fa06b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:33.314839+00:00
-- url     : https://prove2.me/submissions/5922abc7-687c-42b2-924f-16a1c9ccbe67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
open PI PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]
namespace PI.HeckeProdW
theorem _root_.solution {M : Type*} [Monoid M] (f : Ideles L →* M) (A D : Ideles L) (h : f A = 1) :
    f (A⁻¹ * D) = f D := by
  have h1 : f A⁻¹ = 1 := by
    calc f A⁻¹ = f A⁻¹ * f A := by rw [h, mul_one]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul, h1, one_mul]
end PI.HeckeProdW
