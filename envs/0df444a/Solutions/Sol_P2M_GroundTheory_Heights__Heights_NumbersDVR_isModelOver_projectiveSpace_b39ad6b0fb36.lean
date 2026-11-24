-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isModelOver_projectiveSpace_b39ad6b0fb36
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:18.793046+00:00
-- url     : https://prove2.me/submissions/92382ba6-4432-4d1f-b556-9e7e8fc88ed8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014

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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (n : ℕ) :
    IsModelOver (⊥ : Ideal (MRing (fun _ : Unit => Fin (n + 1)) O)) n where
  multiProj := isMultiProjPrime_bot
  noTorsion := by
    ext a
    simp only [Ideal.mem_comap, Ideal.mem_bot, C_eq_zero]
  dim := by
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
    have hc : Nat.card ((_ : Unit) × Fin (n + 1)) = n + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    norm_cast
    omega
end GroundTheory.Heights₂.Heights.NumbersDVR
