-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.evT_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:41.359799+00:00
-- url     : https://prove2.me/submissions/b30b7a76-b3ed-422b-84a3-383693678b4e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
open Classical
variable {F : Type} [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 F))) : evT (T : Set _) = ∑ w ∈ T, sgl w 1 := by
  apply af_ext
  intro w
  rw [evT_apply, show (∑ w' ∈ T, sgl w' 1) w = evalV F w (∑ w' ∈ T, sgl w' 1) from rfl, map_sum]
  simp only [show ∀ w', evalV F w (sgl w' 1) = Pi.single w' 1 w from fun _ => rfl]
  by_cases hw : w ∈ T
  · rw [if_pos (by exact_mod_cast hw), Finset.sum_eq_single w]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h; exact absurd hw h
  · rw [if_neg (by exact_mod_cast hw)]
    refine (Finset.sum_eq_zero fun b hb => ?_).symm
    have : w ≠ b := fun h => hw (h ▸ hb)
    simp [Pi.single_apply, this]
end PI.UnitaryGroupMassFormula.UJClassMass
