-- Prove2me | solution 1 for PositivityTheory.KReal.degW_laPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:43.35621+00:00
-- url     : https://prove2.me/submissions/66ae2042-99d3-439d-bb79-f33a752e0a8f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Theorems.Thm_PositivityTheory_KReal_cw_init

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) :
    degW (cPair p q) (laPos p q r s n m) = p * n + q * m := by
  unfold degW
  rw [Fintype.sum_sum_type]
  simp only [shiftNu, laPos, add_sub_cancel_right, sub_add_cancel]
  have e : ∀ (P : Prop) [Decidable P] (t : ℕ), |(if P then (t : ℚ) else 0)| = if P then (t : ℚ) else 0 := by
    intro P _ t
    split_ifs <;> simp
  simp only [e]
  rw [cw_init hp, cw_init hq]
end PositivityTheory.KReal
