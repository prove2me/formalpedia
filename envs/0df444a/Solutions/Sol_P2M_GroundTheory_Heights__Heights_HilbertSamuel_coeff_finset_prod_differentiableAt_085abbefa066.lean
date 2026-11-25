-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_finset_prod_differentiableAt_085abbefa066
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:19.248541+00:00
-- url     : https://prove2.me/submissions/d3dfc2ff-59a2-44c6-ba07-3cffb4898c01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceCoefficientsHolomorphic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {d : ℕ} {ι : Type*} (S : Finset ι)
    (P : ι → (Fin d → ℂ) → Polynomial ℂ) (y₀ : Fin d → ℂ)
    (hP : ∀ i ∈ S, ∀ k, DifferentiableAt ℂ (fun y => (P i y).coeff k) y₀) :
    ∀ k, DifferentiableAt ℂ (fun y => (∏ i ∈ S, P i y).coeff k) y₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert a S ha ih =>
    intro k
    have ih' := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
    exact DifferentiableAt.fun_sum fun p _ =>
      (hP a (Finset.mem_insert_self a S) p.1).mul (ih' p.2)
end GroundTheory.Heights₂.Heights.HilbertSamuel
