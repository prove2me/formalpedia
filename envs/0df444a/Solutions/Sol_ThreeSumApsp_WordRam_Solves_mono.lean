-- Prove2me | solution 1 for ThreeSumApsp.WordRam.Solves.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:10.707922+00:00
-- url     : https://prove2.me/submissions/98999214-ba70-4063-9c58-f99bff1a3bfe

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
namespace Solves
theorem _root_.solution {prob : Problem} {P : List Instr} {b b' : ℕ} {dom dom' : prob.Inst → Prop}
    {T T' : prob.Inst → ℝ} (h : Solves prob P b dom T) (hb : b ≤ b') (hdom : ∀ x, dom' x → dom x)
    (hT : ∀ x, dom' x → T x ≤ T' x) : Solves prob P b' dom' T' := by
  intro x hx bits hadm
  obtain ⟨t, verdict, c, ht, he, ha⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  exact ⟨t, verdict, c, ht.trans (hT x hx), he, ha⟩
end Solves
end ThreeSumApsp.WordRam
