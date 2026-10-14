-- Prove2me | solution 1 for PersistClust.Count.prom_copy_of_bar_partner
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T20:25:05.814289+00:00
-- url     : https://prove2.me/submissions/b757ddd8-1422-4208-98b8-0a801eae8bb2

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    {ε : ℝ} {a : offD (mult (rankFn stageX JX))} {b d b₂ v : ℝ}
    (hpt : offPt a = ((b : EReal), (d : EReal)))
    (hbox1 : b - ε ≤ b₂) (hbox2 : b₂ ≤ b + ε) (hbox3 : d - ε ≤ v) (hbox4 : v ≤ d + ε)
    (hsep : d + 2 * ε < b)
    (hmult : mult (rankFn stageY JY) ((b₂ : EReal), (v : EReal)) ≠ 0) :
    ∃ q : offD (mult (rankFn stageY JY)), CloseCopy2 ε a q := by
  have h0 : ((0 : ℕ) : ℕ∞) < mult (rankFn stageY JY) ((b₂ : EReal), (v : EReal)) :=
    pos_iff_ne_zero.mpr hmult
  refine ⟨⟨(((b₂ : EReal), (v : EReal)), (0 : ℕ)), h0⟩, ?_⟩
  have e1 : (b : EReal) ≤ (b₂ : EReal) + (ε : EReal) := by
    rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith)
  have e2 : (b₂ : EReal) ≤ (b : EReal) + (ε : EReal) := by
    rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith)
  have e3 : (d : EReal) ≤ (v : EReal) + (ε : EReal) := by
    rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith)
  have e4 : (v : EReal) ≤ (d : EReal) + (ε : EReal) := by
    rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith)
  unfold CloseCopy2
  rw [hpt]
  exact ⟨⟨e1, e2⟩, e3, e4⟩
