-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:45.355799+00:00
-- url     : https://prove2.me/submissions/f04a9189-cde5-4ca3-b5f9-1602f05e7aeb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum

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
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable {P}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {T T' : (ι → E) → (ι → E)} {c c' : K} (h : QT P T c) (hT : ∀ t, T' t = T t) (hc : c' = c) :
    QT P T' c' := by
  have hTT : T' = T := funext hT
  subst hTT
  subst hc
  exact h
end PI.TwistedEisensteinNonvanishing.W
