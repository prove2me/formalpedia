-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_coeff_killB_d6e25e411cc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:39.544849+00:00
-- url     : https://prove2.me/submissions/1653ddeb-88e8-485b-8860-c8553a1008c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_monomial_211997d7462a

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
open GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
open Classical
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
theorem _root_.solution (B : Set K) (p : MRing ι R) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (killB B p) = if ∀ v ∈ d.support, v.1 ∉ B then coeff d p else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [killB_monomial]
    by_cases hed : e = d
    · subst hed
      split_ifs <;> simp
    · split_ifs <;> simp [coeff_monomial, hed]
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq]
    split_ifs <;> simp
end GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
