-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.components_of_D1_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:40.74161+00:00
-- url     : https://prove2.me/submissions/d9a36516-ffda-400d-9eec-d9d0e6e9f86f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ChiZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ComponentsOfD1EqZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_openKer_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_smul_bas_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_trE_apply
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
variable [SecondCountableTopology (Fv F v ⊗[F] E)]
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
theorem _root_.solution (h : ¬ OpenKer v ψ) : D1 (E := E) v ψ = {0} := by
  ext y
  constructor
  · intro hy
    by_contra hne
    have h1 : trE (E := E) v y ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact hne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
    apply h (openKer_of v ψ (trE (E := E) v y j) hj fun c hc => ?_)
    have e : c * trE (E := E) v y j =
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c • bas (E := E) v j) * y) := by
      rw [trE_apply, trC_apply, smul_mul_assoc, map_smul, smul_eq_mul]
    rw [e]
    exact hy _ (smul_bas_mem v hc j)
  · intro hy
    rw [Set.mem_singleton_iff.1 hy]
    intro x _
    simp [psiV_zero]
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
