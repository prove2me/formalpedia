-- Prove2me | solution 1 for TopkisRation.Myopic.C_flat_below
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:01:56.972427+00:00
-- url     : https://prove2.me/submissions/cb8fc670-4eb4-4bd4-b28c-e9668683479b

import Definitions.Def_TopkisRation_Myopic_MultiPeriod
open TopkisRation.Myopic

private theorem recursion {n : ℕ} (Q : MultiModel n) {m : ℕ}
    (hm : m ∈ Finset.Icc 1 Q.N) (w : ℝ) :
    Q.C m w = sInf (Q.gtilde m '' Set.Ici (max w 0)) := by
  have hm' := Finset.mem_Icc.mp hm
  have heq : Q.N + 1 - m = (Q.N - m) + 1 := by omega
  have heq' : Q.N - (Q.N - m) = m := by omega
  have hidx : Q.N + 1 - (m + 1) = Q.N - m := by omega
  unfold MultiModel.gtilde MultiModel.C
  simp only [heq, MultiModel.Crev, heq', hidx]

theorem solution {n : ℕ} (Q : MultiModel n) (hQ : Q.Standing)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 Q.N)
    (x : ℝ) (hx : 0 ≤ x)
    (hmin : ∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) :
    (∀ w, w ≤ x → Q.C m w = Q.C m x) ∧
    ∀ w, x ≤ w → Q.C m x ≤ Q.C m w := by
  have hbd (w : ℝ) : BddBelow (Q.gtilde m '' Set.Ici (max w 0)) := by
    refine ⟨Q.gtilde m x, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hmin z ((le_max_right w 0).trans hz)
  have hne (w : ℝ) : (Q.gtilde m '' Set.Ici (max w 0)).Nonempty :=
    ⟨_, ⟨max w 0, Set.mem_Ici.mpr le_rfl, rfl⟩⟩
  have hval (w : ℝ) (hw : w ≤ x) : Q.C m w = Q.gtilde m x := by
    rw [recursion Q hm w]
    apply le_antisymm
    · exact csInf_le (hbd w) ⟨x, max_le hw hx, rfl⟩
    · apply le_csInf (hne w)
      rintro _ ⟨z, hz, rfl⟩
      exact hmin z ((le_max_right w 0).trans hz)
  constructor
  · intro w hw
    rw [hval w hw, hval x le_rfl]
  · intro w hw
    rw [hval x le_rfl, recursion Q hm w]
    apply le_csInf (hne w)
    rintro _ ⟨z, hz, rfl⟩
    exact hmin z ((le_max_right w 0).trans hz)

#print axioms solution
