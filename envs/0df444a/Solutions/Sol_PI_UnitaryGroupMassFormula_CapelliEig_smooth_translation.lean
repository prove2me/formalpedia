-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CapelliEig.smooth_translation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:35.5788+00:00
-- url     : https://prove2.me/submissions/9922f388-5cb0-48f0-9522-b1b9293d7897

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_CoreDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Theorems.Thm_PI_UnitaryGroupMassFormula_CapelliEig_coef_smoothOnGV
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CapelliEig
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.CapelliEig
theorem _root_.solution : SmTrans := by
  intro k r ε Hs _ _ σ Wp Wq _ _ _ _ _ _ P₀ hP P Q hQ
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det P₀).mp hP.1.1
  have hw : ∀ w, Formalism.REAL.SmoothOnGV ε (fun x => σ (P₀⁻¹ * x * P₀) (Q w)) := fun w =>
    Formalism.QuantumDeterminants.ioh_smooth ε (Hpk k r) P₀ P₀⁻¹ (fun g => σ g (Q w))
      (Matrix.mul_nonsing_inv P₀ hdet) hP.1.2.symm (hQ w)
  exact ⟨fun w => hw w, coef_smoothOnGV ε _ P Q hw⟩
end PI.UnitaryGroupMassFormula.CapelliEig
