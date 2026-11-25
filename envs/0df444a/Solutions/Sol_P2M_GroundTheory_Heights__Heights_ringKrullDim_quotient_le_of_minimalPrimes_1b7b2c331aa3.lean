-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_of_minimalPrimes_1b7b2c331aa3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:14.64329+00:00
-- url     : https://prove2.me/submissions/6fcce962-fcd6-4326-84b1-c265d65920a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsFibreCompDimZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfChartPointSecPointSpecChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PFibreCompDimZ
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_step_77fe98b2628b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsDedekindDomain
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] (J : Ideal R)
    (k : WithBot ℕ∞) (h : ∀ W ∈ J.minimalPrimes, ringKrullDim (R ⧸ W) ≤ k) :
    ringKrullDim (R ⧸ J) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (show J ≤ l.head.1.asIdeal from l.head.2)
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨l.length, fun i => ⟨(l i).1, show (W : Set R) ⊆ (l i).1.asIdeal from hle.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) W) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ W) := (ringKrullDim_quotient W).symm
    _ ≤ k := h W hW
end GroundTheory.Heights₂.Heights
