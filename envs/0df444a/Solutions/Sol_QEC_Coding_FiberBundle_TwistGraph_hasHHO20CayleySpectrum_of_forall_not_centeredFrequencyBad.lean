-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.hasHHO20CayleySpectrum_of_forall_not_centeredFrequencyBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:35.264245+00:00
-- url     : https://prove2.me/submissions/45c4126f-39e0-45e1-95ed-b702aa5241f3

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_cayleyMultiplier_eq_ofReal_sum_sampledTypeCharacter
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_sampledTypeCharacter_eq_centeredCharacterSum_sub

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (sample : RandomTwist.Sample r typeCount ell)
    (hEll : 100001 ≤ ell)
    (hGood :
      ∀ frequency : ZMod ell, frequency ≠ 0 →
        ¬ CenteredFrequencyBad frequency sample) :
    HasHHO20CayleySpectrum sample := by
  intro frequency hfrequency
  have hCentered :
      |centeredCharacterSum frequency sample| ≤
        (typeCount : Real) / 50000 := by
    exact le_of_not_gt (hGood frequency hfrequency)
  have hEllReal : (100001 : Real) ≤ ell := by
    exact_mod_cast hEll
  have hDen : (100000 : Real) ≤ (ell : Real) - 1 := by
    linarith
  have hDenPos : (0 : Real) < (ell : Real) - 1 :=
    lt_of_lt_of_le (by norm_num) hDen
  have hBiasNonneg :
      (0 : Real) ≤ 2 * typeCount / (ell - 1 : Real) := by
    exact div_nonneg (by positivity) hDenPos.le
  have hBias :
      (2 : Real) * typeCount / (ell - 1 : Real) ≤
        (typeCount : Real) / 50000 := by
    calc
      (2 : Real) * typeCount / (ell - 1 : Real) ≤
          (2 : Real) * typeCount / 100000 := by
        gcongr
      _ = (typeCount : Real) / 50000 := by ring
  have hRaw :
      |∑ τ : Fin typeCount,
          sampledTypeCharacter frequency τ sample| ≤
        2 * typeCount / 50000 := by
    calc
      |∑ τ : Fin typeCount,
          sampledTypeCharacter frequency τ sample| =
          |centeredCharacterSum frequency sample -
            2 * typeCount / (ell - 1 : Real)| := by
        rw [sum_sampledTypeCharacter_eq_centeredCharacterSum_sub]
      _ ≤
          |centeredCharacterSum frequency sample| +
            |2 * typeCount / (ell - 1 : Real)| :=
        abs_sub _ _
      _ =
          |centeredCharacterSum frequency sample| +
            2 * typeCount / (ell - 1 : Real) := by
        rw [abs_of_nonneg hBiasNonneg]
      _ ≤
          (typeCount : Real) / 50000 +
            (typeCount : Real) / 50000 :=
        add_le_add hCentered hBias
      _ = 2 * typeCount / 50000 := by ring
  rw [cayleyMultiplier_eq_ofReal_sum_sampledTypeCharacter,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    (50000 : Real) *
        |∑ τ : Fin typeCount,
          sampledTypeCharacter frequency τ sample| ≤
        50000 * (2 * typeCount / 50000) :=
      mul_le_mul_of_nonneg_left hRaw (by norm_num)
    _ = 2 * typeCount := by ring
end QEC.Coding.FiberBundle.TwistGraph
