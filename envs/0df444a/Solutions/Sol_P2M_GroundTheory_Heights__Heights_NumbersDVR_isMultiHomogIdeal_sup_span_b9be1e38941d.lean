-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_b9be1e38941d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:31.395623+00:00
-- url     : https://prove2.me/submissions/d98dbef7-74ca-44a2-85ed-1aa643ad57c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_iff_isHomogeneous_ee97d9b388e0

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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} {J : Ideal (MRing ι R)} {f : MRing ι R} {s : K → ℕ}
    (hJ : IsMultiHomogIdeal J) (hf : IsMultiHomog f s) :
    IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  rw [isMultiHomogIdeal_iff_isHomogeneous] at hJ ⊢
  refine hJ.sup (Ideal.homogeneous_span _ _ ?_)
  rintro x rfl
  exact ⟨s, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩
end GroundTheory.Heights₂.Heights.NumbersDVR
