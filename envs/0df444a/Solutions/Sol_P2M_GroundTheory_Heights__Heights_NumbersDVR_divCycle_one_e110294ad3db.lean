-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_one_e110294ad3db
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:46.186015+00:00
-- url     : https://prove2.me/submissions/17f12a0f-96d7-4845-b191-a62560575327

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects

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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] (P : Ideal (MRing ι R)) (W : Ideal (MRing ι R)) :
    divCycle P 1 W = 0 := by
  unfold divCycle
  rw [dif_neg]
  rintro ⟨h, -⟩
  have hW : W.IsPrime := h.1.1
  have : P ⊔ Ideal.span {(1 : MRing ι R)} = ⊤ := by
    rw [Ideal.span_singleton_one, sup_top_eq]
  exact hW.ne_top (top_le_iff.mp (this ▸ h.1.2))
end GroundTheory.Heights₂.Heights.NumbersDVR
