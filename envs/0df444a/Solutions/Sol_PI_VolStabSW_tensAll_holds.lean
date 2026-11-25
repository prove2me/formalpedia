-- Prove2me | solution 1 for PI.VolStabSW.tensAll_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:20.521604+00:00
-- url     : https://prove2.me/submissions/e08a13bd-6ca6-40ce-97b1-6473c10e3f18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Theorems.Thm_PI_VolStabSW_TensAllW_lip_field
import Theorems.Thm_PI_VolStabSW_tensFacts_of
import Theorems.Thm_PI_VolStabSW_lip_ainf
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
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW TensAllW
namespace PI.VolStabSW
theorem _root_.solution : TensAll := by
  unfold TensAll
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _
  show TensFacts F E σ M J a (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), TensFacts F E σ M J a (Fv F v)
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  have hUinf : IsOpen {r : Ainf F | IsUnit r} := by
    show IsOpen {r : (∀ w : InfinitePlace F, w.Completion) | IsUnit r}
    have hset : {r : (∀ w : InfinitePlace F, w.Completion) | IsUnit r} =
        ⋂ w : InfinitePlace F, (fun r : (∀ w : InfinitePlace F, w.Completion) => r w) ⁻¹' {x | x ≠ 0} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Pi.isUnit_iff, isUnit_iff_ne_zero]
    rw [hset]
    exact isOpen_iInter_of_finite fun w => isOpen_ne.preimage (continuous_apply w)
  refine ⟨tensFacts_of σ hσ J hJ.1 a (Ainf F) hUinf (lip_ainf F), fun v => ?_⟩
  have hUv : IsOpen {r : Fv F v | IsUnit r} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne
  haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv (F := F) (v := v)
  haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv (F := F) (v := v)
  exact tensFacts_of σ hσ J hJ.1 a (Fv F v) hUv (lip_field _)
end PI.VolStabSW
