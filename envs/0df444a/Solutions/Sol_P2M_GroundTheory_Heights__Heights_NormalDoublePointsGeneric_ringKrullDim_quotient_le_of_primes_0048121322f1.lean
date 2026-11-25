-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_le_of_primes_0048121322f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:46.826258+00:00
-- url     : https://prove2.me/submissions/8227e804-5a1d-466f-bd22-7d763a2bc61b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric

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
open MvPolynomial Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
namespace GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
theorem _root_.solution {R : Type*} [CommRing R] (I : Ideal R) (k : WithBot ℕ∞)
    (h : ∀ W : Ideal R, W.IsPrime → I ≤ W → ∃ K : Ideal R, K ≤ W ∧ ringKrullDim (R ⧸ K) ≤ k) :
    ringKrullDim (R ⧸ I) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨K, hKW, hK⟩ := h l.head.1.asIdeal l.head.1.isPrime l.head.2
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) K) :=
    ⟨l.length, fun i => ⟨(l i).1, show (K : Set R) ⊆ (l i).1.asIdeal from hKW.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) K) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ K) := (ringKrullDim_quotient K).symm
    _ ≤ k := hK
end GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
