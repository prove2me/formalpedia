-- Prove2me | solution 1 for SDDiP.Conv.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:34:46.019395+00:00
-- url     : https://prove2.me/submissions/55cebd25-8625-4b90-b906-4e4a591ece8e

import Mathlib
import Definitions.Def_SDDiP_Conv_SND
import Theorems.Thm_SDDiP_Conv_claim_1
import Theorems.Thm_SDDiP_Conv_eq_3_8
import Theorems.Thm_SDDiP_Conv_sampling_infinitely_often

namespace SDDiP1Aux2

open SDDiP.Conv StochasticProg.Multistage MeasureTheory Filter

variable {H d ℓ : ℕ} (D : Model H d ℓ)

lemma mem_children {n m : D.T.Node} :
    m ∈ D.T.children n ↔ (D.T.stage m).val = (D.T.stage n).val + 1 ∧ D.T.anc m = n := by
  simp [Tree.children]

lemma leaf_children {n : D.T.Node} (hn : D.IsLeaf n) : D.T.children n = ∅ := by
  ext m
  simp only [Finset.notMem_empty, iff_false]
  intro h
  rw [mem_children] at h
  have := (D.T.stage m).isLt
  unfold Model.IsLeaf at hn
  omega

lemma Qcal_leaf {n : D.T.Node} (hn : D.IsLeaf n) (x : Fin d → Bool) : D.Qcal n x = 0 := by
  simp [Model.Qcal, leaf_children D hn]

/-- Induction from the leaves upward. -/
lemma tree_induction (P : D.T.Node → Prop) (h : ∀ n, (∀ m ∈ D.T.children n, P m) → P n) :
    ∀ n, P n := by
  suffices ∀ k, ∀ n, H - (D.T.stage n).val = k → P n from fun n => this _ n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk
    apply h
    intro m hm
    rw [mem_children] at hm
    have := (D.T.stage m).isLt
    exact ih _ (by omega) m rfl

lemma approx_leaf (L : D.T.Node → ℝ) {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d)
    (i : ℕ) {n : D.T.Node} (hn : D.IsLeaf n) (x : Fin d → Bool) : D.approx L s κ i n x = 0 := by
  simp [Model.approx, Model.psi, hn]

lemma stage_iter (x : D.T.Node) : ∀ j ≤ (D.T.stage x).val,
    (D.T.stage ((D.T.anc)^[j] x)).val + j = (D.T.stage x).val := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    rw [Function.iterate_succ_apply']
    have h2 := D.T.anc_stage ((D.T.anc)^[j] x) (by omega)
    omega

lemma exists_leaf_below : ∀ n : D.T.Node, ∃ ℓ' : D.Leaf, D.OnPath ℓ' n := by
  apply tree_induction D
  intro n ih
  by_cases hl : D.IsLeaf n
  · exact ⟨⟨n, hl⟩, 0, Nat.zero_le _, rfl⟩
  · have hlt : (D.T.stage n).val + 1 < H := by
      have := (D.T.stage n).isLt; unfold Model.IsLeaf at hl; omega
    have hsum := D.p_children n hlt
    have hne : (D.T.children n).Nonempty := by
      apply Finset.nonempty_of_sum_ne_zero (f := D.p)
      rw [← hsum]; exact (D.p_pos n).ne'
    obtain ⟨m, hm⟩ := hne
    obtain ⟨ℓ', j, hj, hjm⟩ := ih m hm
    have hst := stage_iter D ℓ'.1 j hj
    rw [hjm] at hst
    have hm' := (mem_children D).1 hm
    refine ⟨ℓ', j + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply', hjm, hm'.2]

end SDDiP1Aux2

open SDDiP.Conv StochasticProg.Multistage MeasureTheory Filter

theorem solution {H d ℓ M : ℕ} (D : Model H d ℓ) (hM : 0 < M) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → Fin M → D.Leaf) (hS : D.IsSampling P S)
    (κ : Ω → ℕ → D.T.Node → Cut d)
    (hvalid : ∀ ω, D.ValidCuts (fun i => S i ω) (κ ω))
    (htight : ∀ ω, D.TightCuts L sol (fun i => S i ω) (κ ω))
    (hfin : ∀ ω, D.FiniteCuts (fun i => S i ω) (κ ω)) :
    ∀ᵐ ω ∂P, ∀ j : ℕ,
      (∀ i ≥ j, D.approx L (fun i => S i ω) (κ ω) i = D.approx L (fun i => S i ω) (κ ω) j) →
        D.IsOptimal (D.forwardSol L sol (fun i => S i ω) (κ ω) j) := by
  filter_upwards [sampling_infinitely_often D hM P S hS] with ω hω
  intro j hconst
  have hfwd : ∀ i ≥ j, D.forwardSol L sol (fun i => S i ω) (κ ω) i =
      D.forwardSol L sol (fun i => S i ω) (κ ω) j := by
    intro i hi
    unfold Model.forwardSol
    rw [hconst i hi]
  apply claim_1 D L hL sol hsol (fun i => S i ω) (κ ω) (hvalid ω) j
  apply SDDiP1Aux2.tree_induction D
  intro n ih
  by_cases hl : D.IsLeaf n
  · rw [SDDiP1Aux2.approx_leaf D L _ _ j hl, SDDiP1Aux2.Qcal_leaf D hl]
  · obtain ⟨ℓ', hpath⟩ := SDDiP1Aux2.exists_leaf_below D n
    obtain ⟨i, hi, k, hk⟩ := hω ℓ' j
    have hsamp : D.Sampled ((fun i => S i ω) i) n := ⟨k, by simp only; rw [hk]; exact hpath⟩
    have h := eq_3_8 D L hL sol hsol (fun i => S i ω) (κ ω) (hvalid ω) (htight ω) i n hsamp hl
      (by intro m hm; rw [hconst i hi, hfwd i hi]; exact ih m hm)
    rw [hconst (i + 1) (by omega), hfwd i hi] at h
    exact h

