-- Prove2me | solution 1 for StochasticProg.MultistageBounds.thm1_multistage_jensen_lower_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Gabewhigham
-- created : 2026-09-28T15:53:30.285831+00:00
-- url     : https://prove2.me/submissions/c6165584-09db-487b-8eb6-8218c8e97165

import Mathlib
import Definitions.Def_StochasticProg_MultistageBounds_Tree
import Definitions.Def_StochasticProg_MultistageBounds_Instance

open StochasticProg.MultistageBounds

open scoped Matrix

namespace JensenAggCounterexample

/-- Exact tree: root `0`; stage-1 nodes `1, 2`; stage-2 nodes `3` (child of `1`), `4` (child of `2`). -/
def fineTree : Tree 3 where
  Node := Fin 5
  fintypeNode := inferInstance
  decEqNode := inferInstance
  stage := ![0, 1, 1, 2, 2]
  anc := ![0, 0, 0, 1, 2]
  anc_stage := by decide
  root := 0
  root_stage := by decide
  root_unique := by decide

/-- Aggregated tree: a single path `0 → 1 → 2`. -/
def coarseTree : Tree 3 where
  Node := Fin 3
  fintypeNode := inferInstance
  decEqNode := inferInstance
  stage := ![0, 1, 2]
  anc := ![0, 0, 1]
  anc_stage := by decide
  root := 0
  root_stage := by decide
  root_unique := by decide

noncomputable def fineInst : Instance 3 1 1 fineTree where
  c := fun j _ => (![0, 0, 0, -1, -1] : Fin 5 → ℝ) j
  W := fun _ => 1
  Tmat := fun j => Matrix.of fun _ _ => (![0, 0, 0, 1, 0] : Fin 5 → ℝ) j
  h := fun j _ => (![1, 0, 2, 1, 1] : Fin 5 → ℝ) j
  p := (![1, 1/2, 1/2, 1/2, 1/2] : Fin 5 → ℝ)
  hp_pos := by
    intro k
    fin_cases k <;> norm_num
  hp_sum := by
    intro t
    change ∑ k ∈ Finset.univ.filter
        (fun k : Fin 5 => (![0, 1, 1, 2, 2] : Fin 5 → Fin 3) k = t),
        (![1, 1/2, 1/2, 1/2, 1/2] : Fin 5 → ℝ) k = 1
    rw [Finset.sum_filter, Fin.sum_univ_five]
    fin_cases t <;> simp
    all_goals norm_num

noncomputable def coarseInst : Instance 3 1 1 coarseTree where
  c := fun j _ => (![0, 0, -1] : Fin 3 → ℝ) j
  W := fun _ => 1
  Tmat := fun j => Matrix.of fun _ _ => (![0, 0, 1/2] : Fin 3 → ℝ) j
  h := fun j _ => (![1, 1, 1] : Fin 3 → ℝ) j
  p := fun _ => 1
  hp_pos := by
    intro k
    norm_num
  hp_sum := by
    intro t
    fin_cases t <;> simp [coarseTree] <;> decide

def aggMap : Fin 5 → Fin 3 := ![0, 1, 1, 2, 2]

lemma fine_obj_of_feasible (x : fineTree.Node → Fin 1 → ℝ) (hx : Feasible fineInst x) :
    obj fineInst x = -1 := by
  have h0 := (hx (0 : Fin 5)).2
  have h1 := (hx (1 : Fin 5)).2
  have h2 := (hx (2 : Fin 5)).2
  have h3 := (hx (3 : Fin 5)).2
  have h4 := (hx (4 : Fin 5)).2
  have e0 := congrFun h0 0
  have e1 := congrFun h1 0
  have e2 := congrFun h2 0
  have e3 := congrFun h3 0
  have e4 := congrFun h4 0
  simp [fineInst, fineTree, transitionTerm, Matrix.mulVec, dotProduct] at e0 e1 e2 e3 e4
  simp [obj, fineInst, dotProduct]
  change (x (3 : Fin 5) 0) = 1 - x (1 : Fin 5) 0 at e3
  change (∑ j : Fin 5, _) = _
  rw [Fin.sum_univ_five]
  simp [e1, e3, e4]
  norm_num

lemma coarse_obj_of_feasible (x : coarseTree.Node → Fin 1 → ℝ) (hx : Feasible coarseInst x) :
    obj coarseInst x = -1/2 := by
  have e0 := congrFun (hx (0 : Fin 3)).2 0
  have e1 := congrFun (hx (1 : Fin 3)).2 0
  have e2 := congrFun (hx (2 : Fin 3)).2 0
  simp [coarseInst, coarseTree, transitionTerm, Matrix.mulVec, dotProduct] at e0 e1 e2
  simp [obj, coarseInst, dotProduct]
  change (∑ j : Fin 3, _) = _
  rw [Fin.sum_univ_three]
  change x (2 : Fin 3) 0 = 1 - 2⁻¹ * x (1 : Fin 3) 0 at e2
  change x (1 : Fin 3) 0 = 1 at e1
  simp [e1, e2]
  norm_num

lemma fine_feasible : Feasible fineInst (fun j _ => (![1, 0, 2, 1, 1] : Fin 5 → ℝ) j) := by
  intro j
  refine ⟨fun _ => ?_, ?_⟩
  · fin_cases j <;> simp
  · funext i
    fin_cases i
    fin_cases j <;> simp [fineInst, fineTree, transitionTerm, Matrix.mulVec, dotProduct]

lemma coarse_feasible :
    Feasible coarseInst (fun j _ => (![1, 1, 1/2] : Fin 3 → ℝ) j) := by
  intro j
  refine ⟨fun _ => ?_, ?_⟩
  · fin_cases j <;> norm_num
  · funext i
    fin_cases i
    fin_cases j <;> simp [coarseInst, coarseTree, transitionTerm, Matrix.mulVec, dotProduct]
    norm_num

lemma coarse_h_eq (i : Fin 3) : coarseInst.p i • coarseInst.h i =
    ∑ j ∈ Finset.univ.filter (fun j : Fin 5 => aggMap j = i), fineInst.p j • fineInst.h j := by
  rw [Finset.sum_filter, Fin.sum_univ_five]
  funext k
  fin_cases i <;> simp [aggMap, fineInst, coarseInst]
  norm_num

lemma coarse_T_eq (i : Fin 3) : coarseInst.p i • coarseInst.Tmat i =
    ∑ j ∈ Finset.univ.filter (fun j : Fin 5 => aggMap j = i), fineInst.p j • fineInst.Tmat j := by
  ext k l
  rw [Matrix.smul_apply, Finset.sum_filter, Matrix.sum_apply, Fin.sum_univ_five]
  fin_cases i <;> simp [aggMap, fineInst, coarseInst]

end JensenAggCounterexample

open JensenAggCounterexample in
theorem solution : ¬ (∀ {H n m : ℕ}
    (TFine TCoarse : Tree H)
    (fine : Instance H n m TFine) (coarse : Instance H n m TCoarse)
    (agg : TFine.Node → TCoarse.Node)
    (hagg_root : agg TFine.root = TCoarse.root)
    (hagg_stage : ∀ j : TFine.Node, TCoarse.stage (agg j) = TFine.stage j)
    (hagg_anc : ∀ j : TFine.Node, (TFine.stage j).val ≠ 0 →
      agg (TFine.anc j) = TCoarse.anc (agg j))
    (hW_agree : fine.W = coarse.W)
    (hc_agree : ∀ j : TFine.Node, fine.c j = coarse.c (agg j))
    (hCoarse_h : ∀ i : TCoarse.Node,
      coarse.p i • coarse.h i =
        ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • fine.h j)
    (hCoarse_T : ∀ i : TCoarse.Node, (TCoarse.stage i).val ≠ 0 →
      coarse.p i • coarse.Tmat i =
        ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • fine.Tmat j)
    (Θ : Type) (curOutcome : TCoarse.Node → Θ)
    (hCommonOutcome : ∀ i i' : TCoarse.Node, TCoarse.stage i = TCoarse.stage i' →
      curOutcome i = curOutcome i' → coarse.h i = coarse.h i' ∧ coarse.Tmat i = coarse.Tmat i')
    (zFine zCoarse : ℝ)
    (hzFine_lb : ∀ x, Feasible fine x → zFine ≤ obj fine x)
    (hzFine_attain : ∃ x, Feasible fine x ∧ obj fine x = zFine)
    (hzCoarse_lb : ∀ x, Feasible coarse x → zCoarse ≤ obj coarse x)
    (hzCoarse_attain : ∃ x, Feasible coarse x ∧ obj coarse x = zCoarse),
    zCoarse ≤ zFine) := by
  intro hthm
  have key := hthm fineTree coarseTree fineInst coarseInst aggMap
    rfl
    (by intro j; fin_cases j <;> rfl)
    (by intro j _; fin_cases j <;> rfl)
    rfl
    (by intro j; fin_cases j <;> rfl)
    (fun i => coarse_h_eq i)
    (fun i _ => coarse_T_eq i)
    Unit (fun _ => ())
    (by
      intro i i' hs _
      have : i = i' := by
        fin_cases i <;> fin_cases i' <;> first | rfl | exact absurd hs (by decide)
      subst this
      exact ⟨rfl, rfl⟩)
    (-1) (-1/2)
    (fun x hx => (fine_obj_of_feasible x hx).ge)
    ⟨_, fine_feasible, fine_obj_of_feasible _ fine_feasible⟩
    (fun x hx => (coarse_obj_of_feasible x hx).ge)
    ⟨_, coarse_feasible, coarse_obj_of_feasible _ coarse_feasible⟩
  norm_num at key
