-- Prove2me | solution 1 for ReflectedRWLDP.SamplePath.lemma_4_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T20:48:57.655185+00:00
-- url     : https://prove2.me/submissions/30c74db0-e4cb-4d5a-b0c3-8fd7f6f47d58
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction
import Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_6_i
import Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_6_ii

open MeasureTheory Filter Topology Set
open scoped ENNReal

open ReflectedRWLDP.SamplePath in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    (∀ t y T : ℝ, 0 ≤ t → 0 ≤ y → 0 < T →
      limsup (fun x : ℝ => speedLog x
          (P {ω | ENNReal.ofReal (x * T) <
            ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)})) atTop ≤
        ((t * y : ℝ) : EReal) + (T : EReal) * BellWilliams2001.ThresholdPolicy.logMGF P (U 0) t) ∧
    ∀ y T : ℝ, 0 ≤ y → 0 < T →
      limsup (fun x : ℝ => speedLog x
          (P {ω | 1 ≤ ∫⁻ s in Ioo 0 T,
            ENNReal.ofReal ((lindley (x * y) U ⌊s * x⌋₊ ω / x) ^ p)})) atTop ≤
        -((VTstar P U p T y : ℝ≥0∞) : EReal) :=
  ⟨lemma_4_6_i P U p h, lemma_4_6_ii P U p h⟩
