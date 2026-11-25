-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_of_blockDeg_67d1b71a46e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:47.6273+00:00
-- url     : https://prove2.me/submissions/29338a43-fda8-4072-b61e-19eab722c5dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_blockDeg_b5265fab4acc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution [Fintype K] {I : Ideal (MRing ι F)}
    (h : ∀ (k : K) (n : ℕ), ∀ r ∈ I, weightedHomogeneousComponent (blockDeg k) n r ∈ I) :
    IsMultiHomogIdeal I := by
  classical
  intro r hr b
  let G : Finset K → MRing ι F := fun T =>
    ∑ d ∈ r.support.filter (fun d => ∀ k ∈ T, Finsupp.weight (blockWeight ι) d k = b k),
      monomial d (coeff d r)
  have hG : ∀ T d, coeff d (G T) =
      if ∀ k ∈ T, Finsupp.weight (blockWeight ι) d k = b k then coeff d r else 0 := by
    intro T d
    simp only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter,
      mem_support_iff]
    by_cases hc : coeff d r = 0 <;> simp [hc]
  have hmem : ∀ T, G T ∈ I := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : G ∅ = r := by
        ext d
        rw [hG]
        simp
      rw [this]
      exact hr
    | insert k T hk ih =>
      have : G (insert k T) = weightedHomogeneousComponent (blockDeg k) (b k) (G T) := by
        ext d
        rw [hG, coeff_weightedHomogeneousComponent, hG, weight_blockDeg]
        simp only [Finset.forall_mem_insert, ite_and]
      rw [this]
      exact h k (b k) _ ih
  have : G Finset.univ = weightedHomogeneousComponent (blockWeight ι) b r := by
    ext d
    rw [hG, coeff_weightedHomogeneousComponent]
    by_cases hw : Finsupp.weight (blockWeight ι) d = b
    · simp [hw]
    · rw [if_neg hw, if_neg]
      exact fun h => hw (funext fun k => h k (Finset.mem_univ k))
  rw [← this]
  exact hmem _
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
