-- Prove2me | solution 1 for PI.AlgValsFin.W.ordF_eq_of_classOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:55:59.519249+00:00
-- url     : https://prove2.me/submissions/bde1ad66-e75a-41ef-ad32-d01c98ddfe62

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_classOf_eq_one_iff
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_ordAt_diag
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_rayUnits_top_iff


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
theorem _root_.solution (a : Ideles L) (ha : classOf L a = 1) :
    ∃ k : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), ordF w k = ordAt L w a := by
  obtain ⟨k, u, hu, rfl⟩ := (classOf_eq_one_iff L a).1 ha
  refine ⟨k, fun w => ?_⟩
  rw [ordAt_mul, ordAt_diag, (ordAt_eq_zero_iff L w u).2 ((rayUnits_top_iff L u).1 hu w), add_zero]
  rfl
end PI.AlgValsFin.W
