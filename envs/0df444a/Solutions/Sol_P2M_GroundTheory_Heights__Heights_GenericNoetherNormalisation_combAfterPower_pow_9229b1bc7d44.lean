-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_combAfterPower_pow_9229b1bc7d44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:23.710069+00:00
-- url     : https://prove2.me/submissions/244b81d1-082f-4b71-a2c7-6dc27e322030

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_mul_left_ffaa3113eac1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_sum_fdb7801f7f4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_smul_ec967148cc37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_mem_bea31bfbe550

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
open Polynomial MvPolynomial Ideal Nat RingHom List
open GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}
variable {c : A} {z : Fin m → D} {s : Finset D}
namespace GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
theorem _root_.solution [DecidableEq D] (w : D) (N : ℕ) (b : ℕ → MvPolynomial (Fin m) A)
    (hrel : c • w ^ N = ∑ i ∈ Finset.range N, aeval z (b i) * w ^ i) (j : ℕ) :
    CombAfterPower c z ((Finset.range N).image (fun i ↦ w ^ i)) (w ^ j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  by_cases hj : j < N
  · exact CombAfterPower.of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.2 hj))
  · replace hj := not_lt.mp hj
    apply CombAfterPower.of_smul
    have e : c • w ^ j = ∑ i ∈ Finset.range N, aeval z (b i) * w ^ (i + (j - N)) := by
      have : w ^ j = w ^ (j - N) * w ^ N := by rw [← pow_add, Nat.sub_add_cancel hj]
      rw [this, ← mul_smul_comm, hrel, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [pow_add]
      ring
    rw [e]
    exact CombAfterPower.sum _ _ fun i hi ↦ CombAfterPower.mul_left _
      (ih _ (by have := Finset.mem_range.1 hi; omega))
end GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
