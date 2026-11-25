-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_of_form_8aa08999bb53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:34.840472+00:00
-- url     : https://prove2.me/submissions/131572b9-97ea-4928-b7c0-f0ac5897fcfd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mem_span_of_isMultiHomog_d96bdcb4c476

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
theorem _root_.solution {R : Type*} [CommRing R] {K : Type*} [DecidableEq K]
    {ι : K → Type*} {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) {s : MRing ι R}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  intro f hf b
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hI y hy b))
    (Ideal.mem_sup_right (weightedHomogeneousComponent_mem_span_of_isMultiHomog hs hz b))
end GroundTheory.Heights₂.Heights.NumbersDVR
