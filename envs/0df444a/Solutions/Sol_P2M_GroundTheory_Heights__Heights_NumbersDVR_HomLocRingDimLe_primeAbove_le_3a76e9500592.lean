-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_le_3a76e9500592
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:23.966036+00:00
-- url     : https://prove2.me/submissions/b0c88ac8-72f1-4531-b1c3-9b0db562c60d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_mem_primeAbove_933b8ede3481
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
theorem _root_.solution [Fintype K] (hloc : HomLocRingIsLocal.Statement.{u}) (hPW : P ≤ W)
    (hW : W.IsPrime) (hrel : IsRelevant W) (q : Ideal (homLocRing P W)) [hq : q.IsPrime] :
    primeAbove hPW hW hrel q ≤ W := by
  intro h hh
  rw [mem_primeAbove] at hh
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) h,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp h)]
  refine W.sum_mem fun b _ => ?_
  by_contra hf
  obtain ⟨g, hg, hgW⟩ := homLocRing_form_not_mem hW hrel b
  have hfb : IsMultiHomog (weightedHomogeneousComponent (blockWeight ι) b h) b :=
    weightedHomogeneousComponent_isWeightedHomogeneous b h
  obtain ⟨a, ha, hav⟩ := hh b g hg hgW
  have hu := ((hloc R K ι P W hW hPW).2 b _ g hfb hg hgW (div_mem hfb hg hgW)).2 hf
  have : a = ⟨_, div_mem hfb hg hgW⟩ := Subtype.ext hav
  rw [this] at ha
  exact hq.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
