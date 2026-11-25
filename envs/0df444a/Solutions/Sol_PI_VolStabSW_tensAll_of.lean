-- Prove2me | solution 1 for PI.VolStabSW.tensAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:38.143443+00:00
-- url     : https://prove2.me/submissions/8803b1cb-b819-4e64-90ce-b19f160d01be

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibDis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExOmTOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibTop
import Theorems.Thm_PI_VolStabSW_tensFacts_of_fib
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (h : FreeOpen) : TensAll := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet
  have hF := h F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  exact ⟨tensFacts_of_fib σ M J a (Ainf F) hσ hJ.1 hF.1,
    fun v => by
      haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv (F := F) (v := v)
      haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv (F := F) (v := v)
      exact tensFacts_of_fib σ M J a (Fv F v) hσ hJ.1 (hF.2 v)⟩
end PI.VolStabSW
