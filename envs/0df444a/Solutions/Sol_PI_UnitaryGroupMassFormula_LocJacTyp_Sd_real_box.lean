-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.real_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:15:34.155376+00:00
-- url     : https://prove2.me/submissions/43b2db15-7f33-47d4-873b-10d51bdaaac5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_IsCompactDbox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_SdNormHolds
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
theorem _root_.solution (ι : Type) [Fintype ι] (lam : Measure (Fv F v ⊗[F] E)) [SigmaFinite lam]
    (s : NNReal) (S : Set (Fv F v ⊗[F] E)) :
    ((s • Measure.pi (fun _ : ι => lam)) (Set.univ.pi fun _ => S)).toReal =
      (s : ℝ) * (lam S).toReal ^ Fintype.card ι := by
  rw [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, ENNReal.coe_toReal]
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
