-- Prove2me | solution 1 for ProjSchedMinCut.Transform.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:21:36.339259+00:00
-- url     : https://prove2.me/submissions/5127bdd0-17c7-47eb-8718-6f4e37ae265f

import Definitions.Def_ProjSchedMinCut_Transform_Setting
import Theorems.Thm_ProjSchedMinCut_Transform_xOfCut_injOn
import Theorems.Thm_ProjSchedMinCut_Transform_lemma_2
import Theorems.Thm_ProjSchedMinCut_Transform_lemma_3
import Theorems.Thm_ProjSchedMinCut_Transform_lemma_4

open ProjSchedMinCut.Transform
open Instance

/-- Theorem 1, p. 7: the mapping (7) is a one-to-one correspondence between the `n`-cuts of `D`
of finite capacity and the feasible solutions of (1)–(5); the capacity of such a cut equals the
cost of its image; and the capacity of a minimum `a`-`b`-cut equals the value of an optimal
solution of (1)–(5). -/
theorem solution {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    Set.BijOn I.xOfCut {X | I.IsNCut X ∧ I.cutCap X < ⊤} {x | I.IPFeasible x} ∧
    (∀ X, I.IsNCut X → I.cutCap X < ⊤ →
      I.cutCap X = ENNReal.ofReal (I.cost (I.xOfCut X))) ∧
    ((∃ X, I.IsMinCut X) ∧
      ∀ X, I.IsMinCut X → ∃ x, I.IsOptimal x ∧ I.cutCap X = ENNReal.ofReal (I.cost x)) := by
  refine ⟨⟨?_, xOfCut_injOn I hw hfeas, ?_⟩, ?_, lemma_4 I hw hfeas⟩
  · rintro X ⟨hncut, hcap⟩
    exact (lemma_3 I hw hfeas X hncut hcap).1
  · rintro x hx
    obtain ⟨X, hncut, hcap, hxX, _⟩ := lemma_2 I hw hfeas x hx
    exact ⟨X, ⟨hncut, hcap⟩, hxX⟩
  · intro X hncut hcap
    exact (lemma_3 I hw hfeas X hncut hcap).2
