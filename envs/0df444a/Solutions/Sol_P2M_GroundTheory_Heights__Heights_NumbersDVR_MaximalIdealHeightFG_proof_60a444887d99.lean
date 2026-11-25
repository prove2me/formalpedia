-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MaximalIdealHeightFG_proof_60a444887d99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:33.071875+00:00
-- url     : https://prove2.me/submissions/1637ac73-48f2-45b1-9c46-9d06034be5bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMaxHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMaximalIdealHeightFG
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_height_eq_of_isMaximal_mvPolynomial_fin_6b75e0ad698e

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
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace MaximalIdealHeightFG
theorem _root_.solution : MaximalIdealHeightFG.Statement.{u} := by
  intro F _ A _ _ _ _ m hm
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg F A
  let _ : Algebra (MvPolynomial (Fin s) F) A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) F) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) F) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : m.IsPrime := hm.isPrime
  have hR : ringKrullDim (MvPolynomial (Fin s) F) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdim : ringKrullDim A ≤ s := by
    rw [← hR]
    refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin s) F) A)) fun p q hpq => ?_
    exact Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin s) F) hpq
  let n := m.under (MvPolynomial (Fin s) F)
  have : n.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown n m
  rw [height_eq_of_isMaximal_mvPolynomial_fin F s n inferInstance] at h1
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) (hdim.trans ?_)
  rw [h1]
  exact_mod_cast le_self_add
end MaximalIdealHeightFG
end GroundTheory.Heights₂.Heights.NumbersDVR
