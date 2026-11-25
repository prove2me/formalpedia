-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_quotient_prime_066209f46a97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:53:10.432455+00:00
-- url     : https://prove2.me/submissions/c270d91d-f249-470c-816b-cabddf43be5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution {R : Type*} [CommRing R] (Q : Ideal R) [hQ : Q.IsPrime] :
    ringKrullDim (R ⧸ Q) = (Order.coheight (⟨Q, hQ⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
  have hset : PrimeSpectrum.zeroLocus (Q : Set R) = Set.Ici ⟨Q, hQ⟩ := by
    ext x
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact SetLike.coe_subset_coe
  rw [ringKrullDim_quotient, hset, Order.coheight_eq_krullDim_Ici]
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
