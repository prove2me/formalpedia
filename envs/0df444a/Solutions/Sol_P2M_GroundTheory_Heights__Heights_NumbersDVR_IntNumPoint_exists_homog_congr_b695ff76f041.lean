-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_exists_homog_congr_b695ff76f041
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:00.851208+00:00
-- url     : https://prove2.me/submissions/6f5d7819-23b6-4898-872c-c509c9e1d68d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_isMultiHomog_chartMonomial_8b03eb6525b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_chartMonomial_b7a9a7dc5d3e

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
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
theorem _root_.solution (i : ∀ k, ι k) (p : MRing ι F) :
    ∃ N : K → ℕ, ∀ N', N ≤ N' → ∃ h : MRing ι F, IsMultiHomog h N' ∧
      Ideal.Quotient.mk (chartUnitIdeal i) p = Ideal.Quotient.mk (chartUnitIdeal i) h := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun N' _ => ⟨C a * chartMonomial i N', ?_, ?_⟩⟩
    · exact IsWeightedHomogeneous.C_mul (isMultiHomog_chartMonomial i N') a
    · rw [map_mul, mk_chartMonomial, mul_one]
  | add p q hp hq =>
    obtain ⟨Np, hp⟩ := hp
    obtain ⟨Nq, hq⟩ := hq
    refine ⟨Np ⊔ Nq, fun N' hN => ?_⟩
    obtain ⟨a, ha, ha'⟩ := hp N' (le_sup_left.trans hN)
    obtain ⟨b, hb, hb'⟩ := hq N' (le_sup_right.trans hN)
    exact ⟨a + b, IsWeightedHomogeneous.add ha hb, by rw [map_add, map_add, ha', hb']⟩
  | mul_X p s hp =>
    obtain ⟨Np, hp⟩ := hp
    refine ⟨Np + blockWeight ι s, fun N' hN => ?_⟩
    have h1 : Np ≤ N' - blockWeight ι s := fun k => Nat.le_sub_of_add_le (hN k)
    have h2 : N' - blockWeight ι s + blockWeight ι s = N' := by
      funext k
      exact Nat.sub_add_cancel (le_trans (Nat.le_add_left _ _) (hN k))
    obtain ⟨a, ha, ha'⟩ := hp _ h1
    refine ⟨a * X s, ?_, by rw [map_mul, map_mul, ha']⟩
    have := IsWeightedHomogeneous.mul ha (isWeightedHomogeneous_X (R := F) (blockWeight ι) s)
    rwa [h2] at this
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
