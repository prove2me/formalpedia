-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_isMaximal_of_isPrime_of_quotient_dim_le_zero_3c4a7f03bbc5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:37.368257+00:00
-- url     : https://prove2.me/submissions/71adcf26-46e7-4ca7-b2a1-746d66792ded

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {R : Type*} [CommRing R] {K Q : Ideal R}
    (hK : ringKrullDim (R ⧸ K) ≤ 0) (hQ : Q.IsPrime) (hKQ : K ≤ Q) : Q.IsMaximal := by
  have : Ring.KrullDimLE 0 (R ⧸ K) := Ring.krullDimLE_iff.2 (by exact_mod_cast hK)
  have hsurj := Ideal.Quotient.mk_surjective (I := K)
  have : (Q.map (Ideal.Quotient.mk K)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])
  have hmax := Ideal.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk K))
  have := Ideal.comap_isMaximal_of_surjective _ hsurj (K := Q.map (Ideal.Quotient.mk K))
  rwa [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    sup_eq_left.2 hKQ] at this
end GroundTheory.Heights₂.Heights.ComplexSets
