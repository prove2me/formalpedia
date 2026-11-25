-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isCompact_oev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:49.519747+00:00
-- url     : https://prove2.me/submissions/15616348-f4b7-465d-9dc2-9e3a74f84882

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_oev_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_exists_gens
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
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
theorem _root_.solution : IsCompact (OEv (E := E) v) := by
  obtain ⟨m, w, hw, hx⟩ := exists_gens (E := E) v
  have hK : IsCompact (Set.univ.pi fun _ : Fin m => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hcont : Continuous fun c : Fin m → Fv F v => ∑ k, c k • w k :=
    continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const
  have e : OEv (E := E) v = (fun c : Fin m → Fv F v => ∑ k, c k • w k) ''
      (Set.univ.pi fun _ : Fin m => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    constructor
    · intro h
      obtain ⟨c, hc, rfl⟩ := hx x h
      exact ⟨c, fun k _ => hc k, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun k _ => oev_smul v (hc k trivial) (hw k)
  rw [e]
  exact hK.image hcont
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
