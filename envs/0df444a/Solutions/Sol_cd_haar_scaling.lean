-- Prove2me | solution 1 for cd_haar_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:42.423133+00:00
-- url     : https://prove2.me/submissions/2ed957c7-7ff2-4713-8721-7da233836bfe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CdHaarScale
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_card_false
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_card_true
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_map_phi_indep
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_tie_set


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution : PI.CdHaarScale := by
  intro cd n ε
  by_cases hex : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false)
  · obtain ⟨P₀, Q₀, e₀, h1₀, h2₀⟩ := hex
    have key : ∀ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true)
        (h2 : ∀ j, ε (e (Sum.inr j)) = false),
        (cd.cd P Q).map (phi e h1 h2) = (cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀) := by
      intro P Q e h1 h2
      have hP : P = P₀ := (card_true e h1 h2).symm.trans (card_true e₀ h1₀ h2₀)
      have hQ : Q = Q₀ := (card_false e h1 h2).symm.trans (card_false e₀ h1₀ h2₀)
      subst hP hQ
      have := cd.haar P Q
      exact map_phi_indep e₀ e h1₀ h2₀ h1 h2 (cd.cd P Q)
    have := cd.haar P₀ Q₀
    have hν : (cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀) =
        haarScalarFactor ((cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀)) (Formalism.REAL.muG ε) • Formalism.REAL.muG ε :=
      isMulLeftInvariant_eq_smul _ _
    refine ⟨haarScalarFactor ((cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀)) (Formalism.REAL.muG ε),
      haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
    intro P Q e h1 h2 A hA
    have hp : Measurable (⇑(phi e h1 h2)) := (phi e h1 h2).continuous.measurable
    rw [tie_set e h1 h2 A, ← Measure.map_apply hp hA, key P Q e h1 h2]
    conv_rhs => rw [hν]
    rw [ENNReal.smul_def]
  · refine ⟨1, one_pos, ?_⟩
    intro P Q e h1 h2
    exact absurd ⟨P, Q, e, h1, h2⟩ hex
