-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ne_zero_of_mem_zeroSet_slice_195945c55013
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:57.988133+00:00
-- url     : https://prove2.me/submissions/9268ebad-9fc5-4572-bcda-49846ec60014

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormIntSymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    {x : Fin n → ℂ} (hx : x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) : x ≠ 0 := by
  rintro rfl
  have h1 := hx (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.subset_span rfl))
  simp [linForm] at h1
end GroundTheory.Heights₂.Heights
