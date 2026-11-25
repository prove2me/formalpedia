-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_isPrime_bad04a5b82d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:46.71294+00:00
-- url     : https://prove2.me/submissions/9c897283-389d-4afe-a753-00ead9d8e3fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_frac_one_e27c519d0e78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_form_mem_primeSet_5fb772a85b7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_of_form_mem_812c7e0a7c45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_mem_primeAbove_933b8ede3481
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_multiHomog_c779affea215
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingLocal_proof_56cc4fc2aa55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_proof_5052a3ab7930
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_homLocRing_form_not_mem_76f04394fb55


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
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
theorem _root_.solution [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    (q : Ideal (homLocRing P W)) [hq : q.IsPrime] : (primeAbove hPW hW hrel q).IsPrime := by
  refine MultiHomogPrimeCriterion.proof R K ι _ (primeAbove_multiHomog hPW hW hrel q) ?_ ?_
  · intro htop
    have h1 : (1 : MRing ι R) ∈ primeSet P W q := by
      rw [← mem_primeAbove hPW hW hrel, htop]
      exact Submodule.mem_top
    have hW1 : (1 : MRing ι R) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one W).2 h)
    obtain ⟨a, ha, hav⟩ := valIn_of_form_mem (isWeightedHomogeneous_one R (blockWeight ι))
      (isWeightedHomogeneous_one R (blockWeight ι)) hW1 h1
    rw [frac_one, div_one] at hav
    have : a = 1 := Subtype.ext hav
    exact hq.ne_top ((Ideal.eq_top_iff_one q).2 (this ▸ ha))
  · intro a b sa sb ha hb hab
    obtain ⟨ga, hga, hgaW⟩ := homLocRing_form_not_mem hW hrel sa
    obtain ⟨gb, hgb, hgbW⟩ := homLocRing_form_not_mem hW hrel sb
    have hg : IsMultiHomog (ga * gb) (sa + sb) := IsWeightedHomogeneous.mul hga hgb
    have hgW : ga * gb ∉ W := fun h => (hW.mem_or_mem h).elim hgaW hgbW
    obtain ⟨x, hx, hxv⟩ := valIn_of_form_mem (IsWeightedHomogeneous.mul ha hb) hg hgW hab
    have hxe : x = ⟨_, div_mem ha hga hgaW⟩ * ⟨_, div_mem hb hgb hgbW⟩ := by
      apply Subtype.ext
      rw [hxv, Subring.coe_mul, frac_mul, frac_mul, mul_div_mul_comm]
    rw [hxe] at hx
    rcases hq.mem_or_mem hx with h | h
    · exact Or.inl (form_mem_primeSet hPW ha hga hgaW ⟨_, h, rfl⟩)
    · exact Or.inr (form_mem_primeSet hPW hb hgb hgbW ⟨_, h, rfl⟩)
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
