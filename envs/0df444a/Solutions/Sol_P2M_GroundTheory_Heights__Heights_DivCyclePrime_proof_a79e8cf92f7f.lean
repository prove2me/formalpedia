-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DivCyclePrime_proof_a79e8cf92f7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:15.228648+00:00
-- url     : https://prove2.me/submissions/36d3bc1d-5129-4b42-8540-26c88edd4fea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivCyclePrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_945172d559d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogeneous_of_mem_minimalPrimes_21910d679847

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
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace DivCyclePrime
theorem _root_.solution : DivCyclePrime.Statement := by
  intro n W u hW W' hW'
  have hmem : W' ∈ relComps (W ⊔ Ideal.span {linForm u}) := by
    by_contra hc
    apply Finsupp.mem_support_iff.mp hW'
    simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
    exact if_neg hc
  obtain ⟨hmin, hrel⟩ := hmem
  have hlin : (linForm u : MvPolynomial (Fin n) ℂ) ∈ homogeneousSubmodule (Fin n) ℂ 1 := by
    rw [mem_homogeneousSubmodule]
    exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j
  have hJ : (W ⊔ Ideal.span {linForm u}).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
    ((isHomogIdeal_iff_isHomogeneous W).mp hW.isHomog).sup
      (Ideal.homogeneous_span _ _ fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        exact hx ▸ ⟨1, hlin⟩)
  exact ⟨hmin.1.1, (isHomogIdeal_iff_isHomogeneous W').mpr
    (isHomogeneous_of_mem_minimalPrimes hJ hmin), hrel⟩
end DivCyclePrime
end GroundTheory.Heights₂.Heights
