-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_exists_fwd_antideriv_18f66ff8e357
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:41:18.71219+00:00
-- url     : https://prove2.me/submissions/dde71551-394d-439f-b40f-cc53443b1b98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_eval_aeval_eq_30a4cefc8185
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_antideriv_79b005910f02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b


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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
theorem _root_.solution {K : Type} [DecidableEq K] (D : ℕ) (k : K) (q : MvPolynomial K ℚ)
    (hq : q = 0 ∨ q.totalDegree < D) : ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ D ∧
      ∀ x : K → ℚ, eval (x + Pi.single k 1) P - eval x P = eval x q := by
  rcases hq with rfl | hq
  · exact ⟨0, by simp, fun x => by simp⟩
  obtain ⟨P₀, hd, he⟩ := FieldNumbers.PolyOfDiffs.exists_antideriv k q
  refine ⟨aeval (fun i => X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i)) P₀, ?_, fun x => ?_⟩
  · refine (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (fun i => ?_) P₀).trans (by omega)
    refine (totalDegree_sub _ _).trans ?_
    simp [totalDegree_X, totalDegree_C]
  · have h1 : (fun i => eval (x + Pi.single k 1) (X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i))) = x := by
      funext i; simp
    have h2 : (fun i => eval x (X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i))) = x - Pi.single k 1 := by
      funext i; simp
    rw [eval_aeval_eq, eval_aeval_eq, h1, h2, he x]
end GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
