-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finiteDimensional_piece_458f90289b82
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:59.087423+00:00
-- url     : https://prove2.me/submissions/0abe2813-10ab-49eb-9a98-ab4e79934d56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
theorem _root_.solution (n : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) n) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have hfin : {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = n}.Finite := by
    refine (Finsupp.finite_of_nat_weight_eq (fun _ => (1 : ℕ)) (fun _ => one_ne_zero)
      (∑ k, n k)).subset ?_
    intro d hd
    simp only [Set.mem_ofPred_eq] at hd ⊢
    rw [← hd]
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWeight, smul_eq_mul,
      mul_one]
    rw [Finset.sum_comm]
    simp [Pi.single_apply]
  have := hfin.to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = n})
end GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
