-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpLocalChart_exists_quotient_primes_3a3083b0e3b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:59.1638+00:00
-- url     : https://prove2.me/submissions/bf015862-03b8-4ed9-a745-a62d5271dd03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ComapLiftFormConstChartPrimeExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpLocalChart
theorem _root_.solution {R : Type*} [CommRing R] {K : Type*} {ι : K → Type}
    {J : Type} {P : Ideal (MRing ι R)} {u : J → MRing ι R} {G' : Ideal (MRing (extIdx ι J) R)}
    (hG' : G'.IsPrime) (hQ : blowUpOf P u ≤ G') (hP : P ≤ G'.comap (liftForm (J := J))) :
    ∃ (G₀ : Ideal (MRing ι R ⧸ P)) (W₀ : Ideal (MRing (extIdx ι J) R ⧸ blowUpOf P u)),
      G₀.IsPrime ∧ W₀.IsPrime ∧ G₀.comap (Ideal.Quotient.mk P) = G'.comap (liftForm (J := J)) ∧
        W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = G' := by
  refine ⟨(G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P), G'.map (Ideal.Quotient.mk _),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
    Ideal.comap_map_mk hP, Ideal.comap_map_mk hQ⟩
end BlowUpLocalChart
end GroundTheory.Heights₂.Heights.NumbersDVR
