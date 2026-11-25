-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_isolatedFibrePts_of_le_df5cc0e6337d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:41.21683+00:00
-- url     : https://prove2.me/submissions/7d512987-0fe9-48ca-b260-6e901c02f5a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCountPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedPointsCount

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
open MvPolynomial Topology ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n m : ℕ} {J P : Ideal (MvPolynomial (Fin n) ℂ)} (hJP : J ≤ P)
    (Q : Fin m → MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) {x : Fin n → ℂ}
    (hx : x ∈ isolatedFibrePts J Q z) (hxP : x ∈ zeroSet P) : x ∈ isolatedFibrePts P Q z := by
  obtain ⟨-, hQ, V, hV, hiso⟩ := hx
  exact ⟨hxP, hQ, V, hV, fun x' hx' hQ' => hiso x' ⟨fun q hq => hx'.1 q (hJP hq), hx'.2⟩ hQ'⟩
end GroundTheory.Heights₂.Heights
