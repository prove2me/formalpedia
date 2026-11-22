-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T17:52:39.536378+00:00
-- url     : https://prove2.me/submissions/f2055bc6-c9ff-4522-a228-8abb5220abde

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

private theorem norm_le (M : Machine) (j : ℕ) : M.norm j ≤ M.length := by
  unfold Machine.norm
  split <;> simp_all [Machine.Active]

private theorem control_type (side : Side) (M : Machine) (j : ℕ) :
    (compile side M).nts[iF (M.norm j)]? = some tyF := by
  rw [show iF (M.norm j) = M.norm j + 13 by unfold iF; omega]
  change (List.replicate (M.length + 1) tyF)[M.norm j]? = some tyF
  exact List.getElem?_replicate_of_lt (Nat.lt_succ_of_le (norm_le M j))

private def Checks (G : HORS) (τ : Ty) (t : Tm) : Prop :=
  G.typeOf τ.args t = some .o ∧ τ.homog = true ∧ G.safeTm τ.args t = true

private theorem ctrl_checks (side : Side) (M : Machine) (i : ℕ) :
    Checks (compile side M) tyF (ctrlBody side M i) := by
  cases h : M.lookup i with
  | none => cases side <;> simp only [ctrlBody, h] <;> exact ⟨rfl, rfl, rfl⟩
  | some ins =>
    cases ins <;>
      simp only [ctrlBody, h, callF, Tm.apps, List.foldl, Checks, HORS.typeOf, HORS.safeTm,
        control_type, tb, tz, Tm.vars] <;> exact ⟨rfl, rfl, rfl⟩

private theorem start_checks (side : Side) (M : Machine) :
    Checks (compile side M) .o (startBody M) := by
  simp only [startBody, callF, Tm.apps, List.foldl, Checks, HORS.typeOf, HORS.safeTm, control_type, Tm.vars]
  exact ⟨rfl, rfl, rfl⟩

private theorem rule_checks (side : Side) (M : Machine) (i : ℕ) (hi : i < (compile side M).nts.length) :
    (compile side M).ruleOK i = true ∧ (compile side M).ruleSafe i = true := by
  by_cases h : i < 13
  · interval_cases i <;> first | exact ⟨rfl, rfl⟩ | skip
    obtain ⟨ht, _, hs⟩ := start_checks side M
    exact ⟨beq_iff_eq.mpr ht, hs⟩
  · let j := i - 13
    have eqi : i = j + 13 := by dsimp [j]; omega
    have hj : j < M.length + 1 := by
      simp [compile, arithTys] at hi
      omega
    rw [eqi]
    have hty : (compile side M).nts[j + 13]? = some tyF := List.getElem?_replicate_of_lt hj
    have hr : (compile side M).rules[j + 13]? = some (ctrlBody side M j) := by
      change ((List.range (M.length + 1)).map (ctrlBody side M))[j]? = _
      simp [List.getElem?_range hj]
    simpa [HORS.ruleOK, HORS.ruleSafe, hty, hr, Checks] using ctrl_checks side M j

private theorem proved_here (M : Machine) (side : Side) : (compile side M).Safe := by
  simp only [HORS.Safe, List.all_eq_true, List.mem_range]
  exact fun i hi => (rule_checks side M i hi).2

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (M : Machine) (side : Side) : (compile side M).Safe := proved_here M side
