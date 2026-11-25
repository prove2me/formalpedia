-- Prove2me | solution 1 for PI.AlgValsFin.W.classPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:10:45.445273+00:00
-- url     : https://prove2.me/submissions/2e859791-5d6f-493f-ba9e-86cfe29b63a1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
import Theorems.Thm_PI_AlgValsFin_W_ordAt_eU
import Theorems.Thm_P2M_PI_AlgValsFin_W_ordAt_pow__7347b756aa89
import Theorems.Thm_PI_AlgValsFin_W_ordF_eq_of_classOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution : ClassPow L := by
  classical
  refine ⟨Fintype.card (ClassGroup (𝓞 L)), Fintype.card_pos, fun v => ?_⟩
  have h1 : classOf L (eU v ^ Fintype.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, hk⟩ := ordF_eq_of_classOf _ h1
  refine ⟨k, fun u => ?_⟩
  rw [hk, ordAt_pow', ordAt_eU]
  split_ifs <;> simp
end PI.AlgValsFin.W
