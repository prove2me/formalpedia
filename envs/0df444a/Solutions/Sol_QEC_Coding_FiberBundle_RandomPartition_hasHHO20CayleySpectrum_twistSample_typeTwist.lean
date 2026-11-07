-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.hasHHO20CayleySpectrum_twistSample_typeTwist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:41:02.57872+00:00
-- url     : https://prove2.me/submissions/05989b4b-2261-4c56-904b-46ed4c11e155

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_cayleyMultiplier_twistSample_typeTwist

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    {r typeCount ell : Nat} [NeZero ell]
    (partitionSample : Sample r)
    (spectrumSample : RandomTwist.Sample r typeCount ell)
    (hSpectrum : TwistGraph.HasHHO20CayleySpectrum spectrumSample) :
    TwistGraph.HasHHO20CayleySpectrum
      (twistSample partitionSample
        (fun τ => RandomTwist.typeTwist spectrumSample τ)) := by
  intro frequency hfrequency
  rw [cayleyMultiplier_twistSample_typeTwist]
  exact hSpectrum frequency hfrequency
end QEC.Coding.FiberBundle.RandomPartition
