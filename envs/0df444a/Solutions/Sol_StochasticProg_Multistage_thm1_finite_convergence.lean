-- Prove2me | solution 1 for StochasticProg.Multistage.thm1_finite_convergence
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:34:32.473496+00:00
-- url     : https://prove2.me/submissions/bb18da25-75ab-483c-9e71-5271445c7715

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_Multistage_Instance
import Definitions.Def_StochasticProg_Multistage_Bases
import Definitions.Def_StochasticProg_Multistage_Algorithm

namespace StochasticProg.Multistage.Cex7cf4cf2b

open StochasticProg.Multistage
open scoped Matrix

/-- Two-node tree: root `false` (stage 0), child `true` (stage 1). -/
def T2 : Tree 2 where
  Node := Bool
  fintypeNode := inferInstance
  decEqNode := inferInstance
  stage := fun b => if b then 1 else 0
  anc := fun _ => false
  anc_stage := by
    intro j hj
    cases j <;> simp_all
  root := false
  root_stage := by simp
  root_unique := by
    intro j hj
    cases j <;> simp_all

/-- Root forced to `x = 0` (feasible); child needs `x = 2` but `ub = 1`: infeasible only
because of the bound, which the Step-2 feasibility LP does not model, so no `Step` ever fires. -/
noncomputable def I : Instance 2 1 1 T2 where
  c := fun _ => 0
  W := fun _ => 1
  Tmat := fun _ => 0
  h := fun b _ => if (T2.stage b).val = 0 then (0:ℝ) else 2
  p := fun _ => 1
  hp_pos := fun _ => one_pos
  hp_sum := by
    intro t
    fin_cases t <;> simp [T2] <;> first | decide | rfl
  ub := fun _ _ => 1

lemma child_infeasible (xp x : Fin 1 → ℝ) : ¬ LocalFeasible I (true : T2.Node) xp x := by
  rintro ⟨hb, heq⟩
  have h1 := congrFun heq 0
  have hub := (hb 0).2
  simp [I, T2, transitionTerm, Matrix.one_mulVec] at h1 hub
  linarith

lemma no_step (s s' : State I) : ¬ Step I s s' := by
  intro hs
  cases hs with
  | feas Sf So x θ hopt _ _ _ _ _ _ =>
    exact child_infeasible _ _ (hopt (true : T2.Node)).1.1
  | opt Sf So x θ hopt _ _ _ _ _ _ =>
    exact child_infeasible _ _ (hopt (true : T2.Node)).1.1

theorem cex :
    ¬ ∃ (N : ℕ) (path : ℕ → State I),
      N ≤ Fintype.card (T2.Node × FeasBasis 1 1) + Fintype.card (T2.Node → Basis 1 1) ∧
      path 0 = (∅, ∅) ∧
      (∀ i, i < N → Step I (path i) (path (i + 1))) ∧
      (∀ Sf' So', ¬ Step I (path N) (Sf', So')) ∧
      ((IsRootInfeasible I (path N).1 ∧ ¬ ∃ x, Feasible I x) ∨
        (∃ x : T2.Node → Fin 1 → ℝ, ∃ θ : T2.Node → ℝ,
          (∀ j, IsNodeOptimal I (path N).1 (path N).2 j
              (if (T2.stage j).val = 0 then 0 else x (T2.anc j)) (x j) (θ j)) ∧
          Feasible I x ∧
          (∀ j, (T2.children j).Nonempty → ∀ β : T2.Node → Basis 1 1,
            (∀ k ∈ T2.children j, IsOptimalAt I k (β k) (x j)) →
            θ j ≥ (optCutCoeffs I β j).2 - dotProduct (optCutCoeffs I β j).1 (x j)) ∧
          ∀ x' : T2.Node → Fin 1 → ℝ, Feasible I x' → obj I x ≤ obj I x')) := by
  rintro ⟨N, path, -, h0, hstep, -, hconc⟩
  have hN : N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact h
    · exact absurd (hstep 0 h) (no_step _ _)
  subst hN
  rw [h0] at hconc
  rcases hconc with ⟨hroot, -⟩ | ⟨x, -, -, hfeas, -, -⟩
  · apply hroot
    refine ⟨0, ⟨⟨fun i => ⟨le_refl _, ?_⟩, ?_⟩, ?_⟩⟩
    · simp [I]
    · funext i
      simp [I, T2, transitionTerm]
    · intro p hp; simp at hp
  · exact child_infeasible _ _ (hfeas (true : T2.Node))

end StochasticProg.Multistage.Cex7cf4cf2b

open StochasticProg.Multistage in
open scoped Matrix in
theorem solution : ¬ (∀ {H n m : ℕ} {T : Tree H} (inst : Instance H n m T),
    ∃ (N : ℕ) (path : ℕ → State inst),
      N ≤ Fintype.card (T.Node × FeasBasis n m) + Fintype.card (T.Node → Basis n m) ∧
      path 0 = (∅, ∅) ∧
      (∀ i, i < N → Step inst (path i) (path (i + 1))) ∧
      (∀ Sf' So', ¬ Step inst (path N) (Sf', So')) ∧
      ((IsRootInfeasible inst (path N).1 ∧ ¬ ∃ x, Feasible inst x) ∨
        (∃ x : T.Node → Fin n → ℝ, ∃ θ : T.Node → ℝ,
          (∀ j, IsNodeOptimal inst (path N).1 (path N).2 j
              (if (T.stage j).val = 0 then 0 else x (T.anc j)) (x j) (θ j)) ∧
          Feasible inst x ∧
          (∀ j, (T.children j).Nonempty → ∀ β : T.Node → Basis n m,
            (∀ k ∈ T.children j, IsOptimalAt inst k (β k) (x j)) →
            θ j ≥ (optCutCoeffs inst β j).2 - dotProduct (optCutCoeffs inst β j).1 (x j)) ∧
          ∀ x' : T.Node → Fin n → ℝ, Feasible inst x' → obj inst x ≤ obj inst x'))) := by
  intro hall
  exact StochasticProg.Multistage.Cex7cf4cf2b.cex (hall StochasticProg.Multistage.Cex7cf4cf2b.I)
