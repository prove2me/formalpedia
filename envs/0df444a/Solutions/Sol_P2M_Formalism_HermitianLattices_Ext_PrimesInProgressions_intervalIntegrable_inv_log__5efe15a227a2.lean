-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_inv_log__5efe15a227a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:13.372495+00:00
-- url     : https://prove2.me/submissions/3236c52f-fc34-4840-92c0-7e8e51a1e198

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have h1 : ∀ t ∈ Set.uIcc a b, 1 < t := fun t ht => lt_of_lt_of_le (lt_min ha hb) ht.1
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (lt_trans zero_lt_one (h1 t ht)))
  · intro t ht
    exact ne_of_gt (Real.log_pos (h1 t ht))
end Formalism.HermitianLattices.Ext.PrimesInProgressions
