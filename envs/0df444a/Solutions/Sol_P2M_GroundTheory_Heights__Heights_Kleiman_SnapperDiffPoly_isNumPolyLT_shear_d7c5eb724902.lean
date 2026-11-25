-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_shear_d7c5eb724902
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:26:59.944212+00:00
-- url     : https://prove2.me/submissions/40924a5d-ecac-4dc2-8da6-693882bc5354

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_comp_26fb9bdb9ce0

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
theorem _root_.solution {t D : ℕ} (ν : Fin t → ℤ) {F : (Fin t → ℕ) → ℤ → ℚ} (hF : IsNumPolyLT t D F) :
    IsNumPolyLT t D (fun n c => F n (c + ∑ i, ν i * (n i : ℤ))) := by
  refine isNumPolyLT_comp (Fin.snoc (α := fun _ => MvPolynomial (Fin (t + 1)) ℚ) (fun i => X i.castSucc)
    (X (Fin.last t) + ∑ i, C (ν i : ℚ) * X i.castSucc)) (fun k => ?_) (fun n _ => n)
    (fun n c => c + ∑ i, ν i * (n i : ℤ)) (fun n c => ?_) (fun n c => rfl) hF
  · induction k using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_X]) ?_)
      refine totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, totalDegree_X]
    | cast i => simp [totalDegree_X]
  · funext k
    induction k using Fin.lastCases with
    | last => simp [numPt]
    | cast i => simp [numPt]
end GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
