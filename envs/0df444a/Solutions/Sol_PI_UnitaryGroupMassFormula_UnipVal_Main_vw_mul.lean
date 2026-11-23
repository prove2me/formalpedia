-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnipVal.Main.vw_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:05.3948+00:00
-- url     : https://prove2.me/submissions/e5a86ca5-72e3-43ee-adbb-c6f085ca710e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnipVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentValuation_VwIntEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnipVal PI.UnitaryGroupMassFormula.UnipVal.Main
open PI.UnipVal
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.UnipVal.Main
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vw w (x * y) = vw w x + vw w y := by
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hx)
      (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hy)]
end PI.UnitaryGroupMassFormula.UnipVal.Main
