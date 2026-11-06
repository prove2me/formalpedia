-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerShortage_rejectedCount_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:06:21.923715+00:00
-- url     : https://prove2.me/submissions/fd702c3e-65cb-4854-8bb0-2755cff7646c

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (history : tensorPowerHistory Ω attempts) (hrequired : required ≤ attempts)
    (hshort : (tensorPowerAcceptedIndices accepts attempts history).card < required) :
    attempts - required + 1 ≤ tensorPowerRejectedCount accepts attempts history := by
  unfold tensorPowerRejectedCount
  omega
end QEC.Semantics.FiniteInstrument
