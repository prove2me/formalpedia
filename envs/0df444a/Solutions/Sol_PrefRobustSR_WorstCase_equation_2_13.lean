-- Prove2me | solution 1 for PrefRobustSR.WorstCase.equation_2_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:17:56.587096+00:00
-- url     : https://prove2.me/submissions/521b930c-1e01-4238-a28e-f85e77783a5d

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

set_option autoImplicit false
open MeasureTheory PrefRobustSR.WorstCase

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) :
    (⨆ l ∈ L, SR P l Z) ≤ SRL P L Z := by
  refine iSup₂_le fun l hl => ?_
  unfold SR SRL
  apply sInf_le_sInf
  apply Set.image_mono
  intro t ht
  exact le_trans (le_iSup₂ (f := fun l (_ : l ∈ L) => gap P l Z t) l hl) ht
