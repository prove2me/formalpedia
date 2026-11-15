-- Prove2me | solution 1 for StableMSR.Recovery.TreeDP.bounded_treewidth_dp
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T18:05:23.220624+00:00
-- url     : https://prove2.me/submissions/916a7e8b-50b5-4fc6-874d-5356f74820a8

import Theorems.Thm_StableMSR_Recovery_DecompositionSearch_finite_decomposition_search
import Theorems.Thm_StableMSR_Recovery_TreeDP_decomposition_dp_exact_optimum
set_option autoImplicit false
open scoped Classical BigOperators
open RobertsonSeymour1986.GM5 StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.TreeDP
/-- Bounded treewidth supplies its own small decomposition before local data are
specified. Every bounded local-data allocation on that decomposition admits an
exact finite DP with linear plan overhead and explicit finite-enumeration bounds.
These are cardinality statements, not interpreter running-time bounds. -/
theorem solution {V X : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (width : ℕ) (htw : TreewidthLE G width) :
    ∃ (T : Type) (ft : Fintype T) (dt : DecidableEq T)
      (tree : SimpleGraph T) (bags : T → Finset V),
      IsTreeDecomposition G tree bags ∧
      (∀ t, (bags t).card ≤ width+1) ∧
      @Fintype.card T ft ≤ Fintype.card V + 1 ∧
      ∀ (data : T → BagData V X) (choices : ℕ),
        (∀ t, (data t).bag = bags t) →
        (∀ t, (data t).Local) →
        (∀ t, (data t).choices.card ≤ choices) →
        ∃ p : Plan V X,
          p.Coherent ∧ p.Local ∧ p.nodes ≤ 2 * Fintype.card V + 1 ∧
          p.AllData (fun d => d.bag.card ≤ width+1 ∧ d.choices.card ≤ choices) ∧
          (∀ cap, (solve cap p).card ≤ choices * (cap+1)) ∧
          (∀ cap,
            p.tableVolume cap ≤ (2 * Fintype.card V + 1) * (choices * (cap+1)) ∧
            p.rawCandidateVolume cap ≤
              (2 * Fintype.card V + 1) * (choices ^ 3 * (cap+1) ^ 2)) ∧
          (∀ (whole : V → X) (j : ℕ) (w : ℝ),
            GlobalEvaluates p whole j w ↔
              (∀ t, (data t).valid whole) ∧
              (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
              (∑ t, (data t).count whole) = j ∧
              (∑ t, (data t).weight whole) = w) ∧
          ∀ cap j, j ≤ cap →
            (∃ whole : V → X, (∀ t, (data t).valid whole) ∧
              (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
              (∑ t, (data t).count whole) = j) →
            ∃ e ∈ solve cap p, ∃ whole : V → X,
              e.2.1 = j ∧ (∀ t, (data t).valid whole) ∧
              (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
              (∑ t, (data t).count whole) = j ∧
              (∑ t, (data t).weight whole) = e.2.2 ∧
              ∀ other : V → X, (∀ t, (data t).valid other) →
                (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag other a) →
                (∑ t, (data t).count other) = j →
                  e.2.2 ≤ ∑ t, (data t).weight other := by
  classical
  obtain ⟨T,ft,tree,bags,htd,hwidth,hsize⟩ :=
    (finite_decomposition_search G width).2 ((finite_decomposition_search G width).1.mpr htw)
  letI : Fintype T := ft
  letI : DecidableEq T := Classical.decEq T
  refine ⟨T,ft,inferInstance,tree,bags,htd,hwidth,hsize,?_⟩
  intro data choices hbag hlocal hchoices
  have htd' : IsTreeDecomposition G tree (fun t => (data t).bag) := by
    simpa only [hbag] using htd
  obtain ⟨root⟩ := htd.1.connected.nonempty
  have hbound : ∀ t, (data t).bag.card ≤ width+1 ∧ (data t).choices.card ≤ choices := by
    intro t
    exact ⟨by rw [hbag]; exact hwidth t,hchoices t⟩
  obtain ⟨p,hcoh,hloc,hnodes,hdata,hroot,hvolume,hsem,hopt⟩ :=
    decomposition_dp_exact_optimum G tree data htd' root (width+1) choices hlocal hbound
  have hnodes' : p.nodes ≤ 2 * Fintype.card V + 1 := by omega
  have hfactor : 2 * Fintype.card T - 1 ≤ 2 * Fintype.card V + 1 := by omega
  refine ⟨p,hcoh,hloc,hnodes',hdata,hroot,?_,hsem,hopt⟩
  intro cap
  exact ⟨(hvolume cap).1.trans (Nat.mul_le_mul_right _ hfactor),
    (hvolume cap).2.trans (Nat.mul_le_mul_right _ hfactor)⟩

