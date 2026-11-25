-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isNumPolyLT_sum_9991b4d10672
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:59.164944+00:00
-- url     : https://prove2.me/submissions/908aa6a9-43ad-450e-ad0c-577c6ad7f7cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {k : Type u} [Field k] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {t D r : ℕ} (g : Fin r → (Fin t → ℕ) → ℤ → ℚ) (h : ∀ m, IsNumPolyLT t D (g m)) :
    IsNumPolyLT t D (fun n c => ∑ m, g m n c) := by
  choose Q hQ hev using h
  refine ⟨∑ m, Q m, ?_, fun n c => by simp [hev, map_sum]⟩
  rcases Nat.eq_zero_or_pos D with hD | hD
  · left
    subst hD
    exact Finset.sum_eq_zero fun m _ => (hQ m).resolve_right (Nat.not_lt_zero _)
  · right
    refine lt_of_le_of_lt (totalDegree_finsetSum _ _) ?_
    rw [Finset.sup_lt_iff (by simpa using hD)]
    intro m _
    rcases hQ m with h0 | h0
    · rw [h0, totalDegree_zero]; exact hD
    · exact h0
end GroundTheory.Heights₂.Heights.Kleiman
