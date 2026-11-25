-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_mem_minimalPrimes_of_mem_e470b56afc04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:31.295831+00:00
-- url     : https://prove2.me/submissions/6e942f3c-c449-4e7c-bb72-6cade8c4576d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_not_lt_lt_of_mem_minimalPrimes__7de09ae16e16

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P W : Ideal R} [P.IsPrime] {s t : R}
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) (htP : t ∉ P) (htW : t ∈ W) :
    W ∈ (P ⊔ Ideal.span {t}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  refine ⟨⟨hWp, sup_le (le_sup_left.trans hW.1.2) (Ideal.span_le.mpr (by simpa using htW))⟩,
    fun q hq hqW => ?_⟩
  have : q.IsPrime := hq.1
  have hPq : P < q := lt_of_le_of_ne (le_sup_left.trans hq.2) fun he =>
    htP (he ▸ hq.2 (le_sup_right (a := P) (Ideal.subset_span rfl)))
  rcases hqW.lt_or_eq with hlt | heq
  · exact (not_lt_lt_of_mem_minimalPrimes' hW hPq hlt).elim
  · exact heq.ge
end GroundTheory.Heights₂.Heights.Inter
