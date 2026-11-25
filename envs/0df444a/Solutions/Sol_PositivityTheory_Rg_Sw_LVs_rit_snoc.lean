-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.rit_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:25.257855+00:00
-- url     : https://prove2.me/submissions/b6fcc6bb-74b3-4388-a6e9-c04c2d8b1741

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (G : M2 n → ℂ) (c : M2 n) :
    ∀ (N : ℕ) (V : Fin N → M2 n), rit (fun y => fderiv ℂ G y (y * c)) N V = rit G (N + 1) (Fin.snoc V c) := by
  intro N
  induction N with
  | zero =>
    intro V
    funext y
    simp only [rit_zero, rit_succ]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
  | succ N ih =>
    intro V
    rw [rit_succ, rit_succ, ih]
    have h1 : (fun i : Fin (N + 1) => (Fin.snoc V c : Fin (N + 2) → M2 n) i.succ) =
        Fin.snoc (fun i : Fin N => V i.succ) c := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_last]
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    have h0 : (Fin.snoc V c : Fin (N + 2) → M2 n) 0 = V 0 := by
      simpa using (Fin.snoc_castSucc (α := fun _ => M2 n) (p := V) (x := c) (i := 0))
    rw [h1, h0]
end PositivityTheory.Rg.Sw.LVs
