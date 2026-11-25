-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_comap_C_eq_bot_4584caeb175e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:28.279826+00:00
-- url     : https://prove2.me/submissions/7bdfe514-57c4-4a4d-8499-5a8ea1e823b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe

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
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {σ : Type*} {ϖ : O} (hϖ : Irreducible ϖ) (Q : Ideal (MvPolynomial σ O)) [Q.IsPrime]
    (h : (C ϖ : MvPolynomial σ O) ∉ Q) : Q.comap (C : O →+* MvPolynomial σ O) = ⊥ := by
  by_contra hne
  have : (Q.comap (C : O →+* MvPolynomial σ O)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hne
  have hm := IsLocalRing.eq_maximalIdeal this
  apply h
  have : ϖ ∈ Q.comap (C : O →+* MvPolynomial σ O) := by
    rw [hm]; exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)
  exact this
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
