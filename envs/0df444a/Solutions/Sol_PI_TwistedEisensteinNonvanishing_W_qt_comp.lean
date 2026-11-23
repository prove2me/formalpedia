-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:12.064302+00:00
-- url     : https://prove2.me/submissions/3d6fa33a-24c3-4089-bdea-b64287ed6434

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
theorem _root_.solution {T1 T2 : (ι → E) → (ι → E)} {c1 c2 : K} (h1 : QT P T1 c1) (h2 : QT P T2 c2) :
    QT P (fun t => T1 (T2 t)) (c2 * c1) := by
  intro a b
  obtain ⟨a1, b1, h1'⟩ := h1 a b
  obtain ⟨a2, b2, h2'⟩ := h2 a1 b1
  refine ⟨a2, b2, fun H hH => ?_⟩
  obtain ⟨g1, r1⟩ := h1' H hH
  obtain ⟨g2, r2⟩ := h2' (fun t => H (T1 t)) g1
  exact ⟨g2, r2.trans (by rw [r1]; ring)⟩
end PI.TwistedEisensteinNonvanishing.W
