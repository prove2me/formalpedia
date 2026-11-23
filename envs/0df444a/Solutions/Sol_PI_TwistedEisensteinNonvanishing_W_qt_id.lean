-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:43.84729+00:00
-- url     : https://prove2.me/submissions/ed5bf19a-ea96-44d5-88e6-f61f81828fbd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne

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
open Loc LocE Function Matrix
variable {E K : Type} [Field E] [NumberField E] [Field K]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {P : HeightOneSpectrum (𝓞 E)} {ι : Type} [Fintype ι] [DecidableEq ι] :
    QT P (fun t : ι → E => t) (1 : K) :=
  fun a b => ⟨a, b, fun _ h => ⟨h, (one_mul _).symm⟩⟩
end PI.TwistedEisensteinNonvanishing.W
