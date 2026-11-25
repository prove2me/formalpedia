-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FundCycleBaseChange_proof_63fe28d8b32b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:57.803953+00:00
-- url     : https://prove2.me/submissions/9c8d41d7-5013-4d27-b8fa-bba99a616f71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFundCycleBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_map_of_flat_9840763cb348
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_comap_mem_minimalPrimes_0a2d3ff74ce5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_map_a70e80c1c816
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRelevant_comap_map_iff_ce9d308ab38f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fundCycle_apply_311d00b01b4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RadicalBaseChange_proof_fda9669ff964
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_eq_one_of_isRadical_c91ebf588e5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_eq_maximalIdeal_of_isRadical_fa5b08ef435e


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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace FundCycleBaseChange
theorem _root_.solution (h : MinimalPrimeComap.Statement) : FundCycleBaseChange.Statement := by
  classical
  intro K L _ _ _ σ n J
  have hc : ∀ I : Ideal (MvPolynomial (Fin n) K), I.IsPrime →
      ∀ P ∈ (I.map (MvPolynomial.map σ)).minimalPrimes, P.comap (MvPolynomial.map σ) = I :=
    fun I hI P hP => h K L σ (Fin n) I hI P hP
  have hrad := RadicalBaseChange.proof
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := K) (S := L)
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange (R := K) (S := MvPolynomial (Fin n) K) (M := L)
      (N := MvPolynomial (Fin n) L) (h := Algebra.IsPushout.out (R := K) (S := MvPolynomial (Fin n) K) (R' := L)
        (S' := MvPolynomial (Fin n) L))
  have hsupp : ∀ W ∈ (fundCycle J).support, W ∈ relComps J := by
    intro W hW
    by_contra hn
    exact Finsupp.mem_support_iff.mp hW (by rw [fundCycle_apply, if_neg hn])
  have hone : ∀ W : Ideal (MvPolynomial (Fin n) K), W.IsPrime → ∀ P,
      P ∈ relComps (W.map (MvPolynomial.map σ)) → localMult (W.map (MvPolynomial.map σ)) P = 1 :=
    fun W hW P hP => localMult_eq_one_of_isRadical (hrad K L σ (Fin n) W hW.isRadical) hP.1
  ext P
  rw [Finsupp.finsetSum_apply, fundCycle_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  split_ifs with hP
  · obtain ⟨hWmin, hPW⟩ := comap_mem_minimalPrimes _ hc hP.1
    have hWrel : P.comap (MvPolynomial.map σ) ∈ relComps J :=
      ⟨hWmin, (isRelevant_comap_map_iff σ P).mpr hP.2⟩
    have hWp : (P.comap (MvPolynomial.map σ)).IsPrime := hWmin.1.1
    have hPp : P.IsPrime := hP.1.1.1
    have : P.LiesOver (P.comap (MvPolynomial.map σ)) := ⟨rfl⟩
    have hmult : localMult (J.map (MvPolynomial.map σ)) P =
        localMult J (P.comap (MvPolynomial.map σ)) :=
      localMult_map_of_flat J _ P (map_eq_maximalIdeal_of_isRadical
        (hrad K L σ (Fin n) _ hWp.isRadical) hPW)
    rw [hmult, Finset.sum_eq_single (P.comap (MvPolynomial.map σ))]
    · rw [fundCycle_apply J, if_pos hWrel,
        fundCycle_apply (Ideal.map (MvPolynomial.map σ) (P.comap (MvPolynomial.map σ))) P,
        if_pos ⟨hPW, hP.2⟩, hone _ hWp P ⟨hPW, hP.2⟩, mul_one]
    · intro W₀ hW₀ hne
      rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W₀) P, if_neg, mul_zero]
      intro hPW₀
      exact hne (hc W₀ (hsupp W₀ hW₀).1.1.1 P hPW₀.1).symm
    · intro hW
      rw [Finsupp.notMem_support_iff.mp hW, zero_mul]
  · refine (Finset.sum_eq_zero fun W hW => ?_).symm
    rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W) P, if_neg, mul_zero]
    intro hPW
    exact hP ⟨mem_minimalPrimes_map _ hc (hsupp W hW).1 hPW.1, hPW.2⟩
end FundCycleBaseChange
end GroundTheory.Heights₂.Heights
