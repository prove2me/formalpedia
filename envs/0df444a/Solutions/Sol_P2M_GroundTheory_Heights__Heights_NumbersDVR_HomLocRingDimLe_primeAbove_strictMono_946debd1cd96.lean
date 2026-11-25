-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_strictMono_946debd1cd96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:51.38238+00:00
-- url     : https://prove2.me/submissions/fae0239c-b42c-4abe-a37f-341f411baa23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_form_mem_primeSet_5fb772a85b7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_of_form_mem_812c7e0a7c45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_mem_primeAbove_933b8ede3481

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
theorem _root_.solution [Fintype K] (hmem : HomLocRingMem.Statement.{u}) (hPW : P ≤ W)
    (hW : W.IsPrime) (hrel : IsRelevant W) {q q' : Ideal (homLocRing P W)} (hlt : q < q') :
    primeAbove hPW hW hrel q < primeAbove hPW hW hrel q' := by
  refine lt_of_le_of_ne (fun h hh => ?_) (fun heq => ?_)
  · rw [mem_primeAbove] at hh ⊢
    intro b g hg hgW
    obtain ⟨a, ha, hav⟩ := hh b g hg hgW
    exact ⟨a, hlt.le ha, hav⟩
  · obtain ⟨x, hx', hx⟩ := SetLike.exists_of_lt hlt
    obtain ⟨b, f, g, hf, hg, hgW, hxv⟩ := (hmem R K ι P W hW hPW x.1).1 x.2
    have h1 : f ∈ primeAbove hPW hW hrel q' := form_mem_primeSet hPW hf hg hgW ⟨x, hx', hxv⟩
    rw [← heq] at h1
    obtain ⟨a, ha, hav⟩ := valIn_of_form_mem hf hg hgW h1
    have hax : a = x := Subtype.ext (hav.trans hxv.symm)
    exact hx (hax ▸ ha)
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
