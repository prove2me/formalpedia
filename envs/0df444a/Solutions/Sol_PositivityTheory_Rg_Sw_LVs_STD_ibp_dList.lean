-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.ibp_dList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:54.935265+00:00
-- url     : https://prove2.me/submissions/8a5b9d5d-cbe6-4887-b0a3-b554170fabcd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_contDiffOn_dc
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_isT_dList
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_ibp_dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution {U : Set (Vr n)} (hU : IsOpen U) :
    ∀ (l : List (Fin n × Fin n)) {F φ : Vr n → ℂ}, ContDiffOn ℝ ∞ F U → IsT U φ →
      ∫ x, F x * dList l φ x = (-1) ^ l.length * ∫ x, dList l.reverse F x * φ x := by
  intro l
  match l with
  | [] => intro F φ _ _; simp [dList]
  | a :: l =>
    intro F φ hF hφ
    have happ : ∀ (l m : List (Fin n × Fin n)) (f : Vr n → ℂ), dList (l ++ m) f = dList l (dList m f) := by
      intro l m f
      induction l with
      | nil => simp [dList]
      | cons b l ih => simp [dList, ih]
    have h1 := ibp_dc hU hF (isT_dList hφ l) a
    have h2 := solution hU l (contDiffOn_dc hU hF a) hφ
    rw [dList, h1, h2, List.reverse_cons, happ]
    simp only [dList, List.length_cons, pow_succ]
    ring
end PositivityTheory.Rg.Sw.LVs.STD
