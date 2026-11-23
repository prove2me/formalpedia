-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.vq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:45.19237+00:00
-- url     : https://prove2.me/submissions/aaf02181-d27d-4439-b87b-8942deb828e0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qE_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
variable {P}
variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
include hN hp hq
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {a w : E} {e : ℤ} (h : a = (qOf P : E) ^ e * w) (hw : UnitAt P w) : vq P a = e := by
  have ha : a ≠ 0 := by
    rw [h]
    exact mul_ne_zero (zpow_ne_zero _ (qE_ne P hp)) hw.1
  obtain ⟨w1, h1, hw1⟩ := vq_spec hN hp hq ha
  exact hN.2.2.2.1 E P hp hq _ _ w1 w hw1.1 hw1.2.1 hw1.2.2 hw.2.1 hw.2.2 (h1.symm.trans h)
end PI.TwistedEisensteinNonvanishing.W
