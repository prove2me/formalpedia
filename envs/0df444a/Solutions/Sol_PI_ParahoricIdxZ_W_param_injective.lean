-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.param_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:32.209279+00:00
-- url     : https://prove2.me/submissions/5dcad2a3-c531-4b7f-ac7d-4bd0224da6ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ParamInjective
import Theorems.Thm_PI_ParahoricIdxZ_W_theta_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {a t : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    Function.Injective (param (t := t) O hϖ J' hJ) := by
  rintro ⟨x, B, D⟩ ⟨x', B', D'⟩ h
  obtain ⟨h1, h2, -, h4⟩ := theta_injective h
  have hx : x = x' := Subtype.ext (Units.ext h1)
  have hD : D = D' := Units.ext h4
  subst hx hD h2
  rfl
end PI.ParahoricIdxZ.W
