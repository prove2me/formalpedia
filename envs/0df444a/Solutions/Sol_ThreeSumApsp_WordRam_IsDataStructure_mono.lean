-- Prove2me | solution 1 for ThreeSumApsp.WordRam.IsDataStructure.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:11.725819+00:00
-- url     : https://prove2.me/submissions/4c4c0ea3-c691-4193-9309-52e07fe9400c

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Theorems.Thm_ThreeSumApsp_Dominated_trans


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter
namespace ThreeSumApsp.WordRam
namespace IsDataStructure
theorem _root_.solution {P Q : List Instr} {qI qJ qOut : ℤ} {b b' : ℕ} {extra : List ℤ}
    {dom dom' : ThinPair → Prop} {Tp Sp Tq Tp' Sp' Tq' : ThinPair → ℝ}
    (h : IsDataStructure P Q qI qJ qOut b extra dom Tp Sp Tq) (hb : b ≤ b')
    (hdom : ∀ x, dom' x → dom x) (hTp : ∀ x, dom' x → Tp x ≤ Tp' x)
    (hSp : ∀ x, dom' x → Sp x ≤ Sp' x) (hTq : ∀ x, dom' x → Tq x ≤ Tq' x) :
    IsDataStructure P Q qI qJ qOut b' extra dom' Tp' Sp' Tq' := by
  intro x hx bits hadm
  obtain ⟨tp, tq, c, htp, htq, hrun, hspace, hserves⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  refine ⟨tp, tq, c, htp.trans (hTp x hx), htq.trans (hTq x hx), hrun, fun a ha => hspace a ?_,
    hserves⟩
  have := hSp x hx
  rcases ha with ha | ha
  · left; linarith
  · right; linarith
end IsDataStructure
end ThreeSumApsp.WordRam
