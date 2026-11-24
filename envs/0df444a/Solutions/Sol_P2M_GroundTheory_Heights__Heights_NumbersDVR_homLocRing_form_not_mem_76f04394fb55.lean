-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_homLocRing_form_not_mem_76f04394fb55
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:44.825061+00:00
-- url     : https://prove2.me/submissions/6d24dc8f-7c53-44a8-ac76-1bec2d8e3dbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {R : Type u} [CommRing R] {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W)
    (c : K → ℕ) : ∃ g : MRing ι R, IsMultiHomog g c ∧ g ∉ W := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hc : c = ∑ k, c k • blockWeight ι ⟨k, i k⟩ := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k)
      (fun k => c k • blockWeight ι ⟨k, i k⟩)
      fun k _ => (isWeightedHomogeneous_X R (blockWeight ι) _).pow _
    rw [← hc] at h
    exact h
  · intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).mp h
    exact hi k (hW.mem_of_pow_mem _ hk)
end GroundTheory.Heights₂.Heights.NumbersDVR
