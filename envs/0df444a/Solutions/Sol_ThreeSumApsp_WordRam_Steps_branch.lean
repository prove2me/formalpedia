-- Prove2me | solution 1 for ThreeSumApsp.WordRam.Steps.branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:35.728731+00:00
-- url     : https://prove2.me/submissions/80c20516-5719-45c4-9b26-d0c9f6b27006

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
namespace ThreeSumApsp.WordRam
namespace Steps
theorem _root_.solution {n l pos pos' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} {v : ℤ} {p : Prop}
    (h : Steps P n c ⟨if v < 0 then l else pos, m⟩) (hv : p ↔ ¬ v < 0) (hpos : pos = pos') :
    (p → Steps P n c ⟨pos', m⟩) ∧ (¬ p → Steps P n c ⟨l, m⟩) := by
  subst hpos
  by_cases hp : p
  · exact ⟨fun _ => by rwa [if_neg (hv.1 hp)] at h, fun h' => absurd hp h'⟩
  · exact ⟨fun h' => absurd h' hp, fun _ => by rwa [if_pos (not_not.1 (mt hv.2 hp))] at h⟩
end Steps
end ThreeSumApsp.WordRam
