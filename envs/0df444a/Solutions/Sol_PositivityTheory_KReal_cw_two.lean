-- Prove2me | solution 1 for PositivityTheory.KReal.cw_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:10.788496+00:00
-- url     : https://prove2.me/submissions/c86d6fe6-da1a-4682-af45-7ac9b1808844

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Theorems.Thm_PI_FockOneDegW_Core_key


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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (G H : ι → ℚ) {a b : ι} (hab : a ≠ b)
    (h : ∀ x, x ≠ a → x ≠ b → G x = H x) : ∑ x, G x = ∑ x, H x + (G b - H b) + (G a - H a) := by
  have key : ∑ x, (G x - H x) = (G a - H a) + (G b - H b) :=
    Fintype.sum_eq_add a b hab (fun x hx => by rw [h x hx.1 hx.2, sub_self])
  rw [Finset.sum_sub_distrib] at key
  linarith
end PositivityTheory.KReal
