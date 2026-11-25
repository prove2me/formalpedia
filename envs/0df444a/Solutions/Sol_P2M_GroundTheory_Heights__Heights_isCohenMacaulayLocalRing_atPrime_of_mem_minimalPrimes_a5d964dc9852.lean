-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes_a5d964dc9852
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:55.026974+00:00
-- url     : https://prove2.me/submissions/53687588-c0c4-422b-ab42-da65347600aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLocusOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMGeneralPoint

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
open MvPolynomial ComplexSets IsLocalRing
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ}
    {I W : Ideal (MvPolynomial (Fin n) ℂ)} [W.IsPrime] (hW : W ∈ I.minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime W))) := by
  set S := Localization.AtPrime W
  set J := I.map (algebraMap (MvPolynomial (Fin n) ℂ) S)
  have hJm : J ≤ maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hW.1.2
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hdim : Ring.KrullDimLE 0 (S ⧸ J) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro K hK
    have : K.IsPrime := hK.1.1
    have hKm : K ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal hK.1.1.ne_top
    have hI : I ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      Ideal.map_le_iff_le_comap.mp hK.1.2
    have hKW : K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) ≤ W := by
      have h := Ideal.comap_mono (f := algebraMap (MvPolynomial (Fin n) ℂ) S) hKm
      rwa [show (maximalIdeal S).comap (algebraMap (MvPolynomial (Fin n) ℂ) S) = W from
        Localization.AtPrime.under_maximalIdeal] at h
    have hWK : W ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      hW.2 ⟨Ideal.IsPrime.comap _, hI⟩ hKW
    have hmK : maximalIdeal S ≤ K := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_le_iff_le_comap.mpr hWK
    rw [le_antisymm hKm hmK]
    exact maximalIdeal.isMaximal S
  have h0 : ringKrullDim (S ⧸ J) = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdim
  exact
    { exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil _ _, by simpa using h0⟩ }
end GroundTheory.Heights₂.Heights
