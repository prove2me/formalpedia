-- Prove2me | solution 1 for QLLL.SAT.exists_assignment_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:57:16.554014+00:00
-- url     : https://prove2.me/submissions/28ab95e6-876c-4ee0-b4da-e69e9a1680a5

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Definitions.Def_QLLL_Classical_InfiniteKSAT
import Theorems.Thm_QLLL_SAT_exists_forall_clause_eval
import Mathlib
import Std.Sat.CNF

-- inline helpers from QuantumLocalLemma.Classical.InfiniteKSAT
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The infinite classical Lovász Local Lemma

`QuantumLocalLemma.Classical.KSAT` proves Corollary 2 for a finite formula: finitely many variables,
finitely many clauses. This file removes both restrictions.

The route is compactness, not a measure-theoretic limit. Two halves:

* `exists_assignment_of_finset'`, a transport of the finite theorem to arbitrary
  variable and index types. For a finite set `T` of clauses only the finitely
  many variables occurring in them matter, so relabelling reduces to the `Fin`
  case already proved.
* `QLLL.Compactness.exists_forall_of_forall_finite`, propositional compactness.

The conclusion holds for **arbitrary** types `V` and `ι`. Neither is assumed
countable, and the proof never needs them to be: `Bool ^ V` is compact by
Tychonoff for any `V`, and the finite intersection property applies to a family
of closed sets of any cardinality.

Note the statement is not about `Std.Sat.CNF`, whose `clauses` field is an
`Array` and hence finite by construction. An infinite instance is a family
`C : ι → CNF.Clause V`, and satisfaction is `∀ i, Clause.eval a (C i) = true`.
-/

namespace QLLL.SAT

open Finset Std.Sat

/-! ## Clauses over an arbitrary variable type -/

theorem mem_clauseVars' {V : Type*} [DecidableEq V] {c : CNF.Clause V} {v : V} :
    v ∈ clauseVars' c ↔ ∃ b, (v, b) ∈ c := by
  simp only [clauseVars', List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨u, b⟩, hmem, rfl⟩
    exact ⟨b, hmem⟩
  · rintro ⟨b, hmem⟩
    exact ⟨(v, b), hmem, rfl⟩

theorem eval_relabelClause {V W : Type*} (g : V → W) (c : CNF.Clause V)
    (a : W → Bool) :
    CNF.Clause.eval a (relabelClause g c) = CNF.Clause.eval (fun v => a (g v)) c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [relabelClause, List.map_cons] at *
    rw [CNF.Clause.eval_cons, CNF.Clause.eval_cons, ih]

theorem clauseVars'_relabelClause {V W : Type*} [DecidableEq V] [DecidableEq W]
    (g : V → W) (c : CNF.Clause V) :
    clauseVars' (relabelClause g c) = (clauseVars' c).image g := by
  ext w
  simp only [mem_clauseVars', Finset.mem_image, relabelClause, List.mem_map]
  constructor
  · rintro ⟨b, ⟨u, v⟩, hu, huv⟩
    exact ⟨u, ⟨v, hu⟩, congrArg Prod.fst huv⟩
  · rintro ⟨u, ⟨b, hb⟩, rfl⟩
    exact ⟨b, (u, b), hb, rfl⟩

/-! ## The finite theorem over arbitrary types -/

/-! ## The infinite theorem -/

end QLLL.SAT


section

open QLLL
open QLLL.SAT
open Finset Std.Sat

theorem solution {V ι : Type*} [DecidableEq V]
    (C : ι → CNF.Clause V) (T : Finset ι) (k D : ℕ) (hk : 1 ≤ k) (hD1 : 1 ≤ D)
    (hvars : ∀ i ∈ T, (clauseVars' (C i)).card = k)
    (hdeg : ∀ v : V, (T.filter fun i => v ∈ clauseVars' (C i)).card ≤ D)
    (hDk : (D : ℝ) * (Real.exp 1 * k) ≤ 2 ^ k) :
    ∃ a : V → Bool, ∀ i ∈ T, CNF.Clause.eval a (C i) = true := by
  classical
  set W : Finset V := T.biUnion (fun i => clauseVars' (C i)) with hWdef
  have hsub : ∀ i ∈ T, clauseVars' (C i) ⊆ W := fun i hi =>
    Finset.subset_biUnion_of_mem (fun i => clauseVars' (C i)) hi
  let eW := W.equivFin
  let g : V → Fin (W.card + 1) := fun v =>
    if h : v ∈ W then (eW ⟨v, h⟩).castSucc else Fin.last W.card
  have hgW : ∀ (v : V) (h : v ∈ W), g v = (eW ⟨v, h⟩).castSucc := by
    intro v h; simp only [g, dif_pos h]
  have hginj : ∀ u ∈ W, ∀ v ∈ W, g u = g v → u = v := by
    intro u hu v hv huv
    rw [hgW u hu, hgW v hv, Fin.castSucc_inj] at huv
    exact congrArg Subtype.val (eW.injective huv)
  let eT := T.equivFin
  let σ : Fin T.card → ι := fun j => ((eT.symm j : {i // i ∈ T}) : ι)
  have hσT : ∀ j, σ j ∈ T := fun j => (eT.symm j).2
  have hσe : ∀ (i : ι) (hi : i ∈ T), σ (eT ⟨i, hi⟩) = i := by
    intro i hi; simp only [σ, Equiv.symm_apply_apply]
  let C' : Fin T.card → CNF.Clause (Fin (W.card + 1)) := fun j =>
    relabelClause g (C (σ j))
  have hC'vars : ∀ j, clauseVars (C' j) = (clauseVars' (C (σ j))).image g := fun j =>
    clauseVars'_relabelClause g (C (σ j))
  have hvars' : ∀ j, (clauseVars (C' j)).card = k := by
    intro j
    rw [hC'vars j, Finset.card_image_of_injOn, hvars (σ j) (hσT j)]
    intro u hu v hv huv
    exact hginj u (hsub _ (hσT j) hu) v (hsub _ (hσT j) hv) huv
  have hdeg' : ∀ v : Fin (W.card + 1),
      (univ.filter fun j => v ∈ clauseVars (C' j)).card ≤ D := by
    intro v
    by_cases hv : ∃ u ∈ W, g u = v
    · obtain ⟨u, huW, rfl⟩ := hv
      have key : ∀ j : Fin T.card,
          (g u ∈ clauseVars (C' j) ↔ u ∈ clauseVars' (C (σ j))) := by
        intro j
        rw [hC'vars j, Finset.mem_image]
        constructor
        · rintro ⟨w, hw, hgw⟩
          exact hginj w (hsub _ (hσT j) hw) u huW hgw ▸ hw
        · intro h; exact ⟨u, h, rfl⟩
      have hcard : (univ.filter fun j : Fin T.card => g u ∈ clauseVars (C' j)).card
          = (T.filter fun i => u ∈ clauseVars' (C i)).card := by
        refine Finset.card_bij' (fun j _ => σ j)
          (fun i hi => eT ⟨i, (Finset.mem_filter.mp hi).1⟩) ?_ ?_ ?_ ?_
        · intro j hj
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨hσT j, (key j).mp hj.2⟩
        · intro i hi
          rw [Finset.mem_filter] at hi ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [key, hσe i hi.1]
          exact hi.2
        · intro j hj
          simp only [σ, Subtype.coe_eta, Equiv.apply_symm_apply]
        · intro i hi
          exact hσe i (Finset.mem_filter.mp hi).1
      rw [hcard]
      exact hdeg u
    · have hempty : (univ.filter fun j : Fin T.card => v ∈ clauseVars (C' j)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j _
        rw [hC'vars j, Finset.mem_image]
        rintro ⟨w, hw, rfl⟩
        exact hv ⟨w, hsub _ (hσT j) hw, rfl⟩
      rw [hempty]
      simp
  obtain ⟨a, ha⟩ := exists_forall_clause_eval C' k D hk hD1 hvars' hdeg' hDk
  refine ⟨fun v => a (g v), fun i hi => ?_⟩
  have h := ha (eT ⟨i, hi⟩)
  have hCi : C' (eT ⟨i, hi⟩) = relabelClause g (C i) := by
    simp only [C', hσe i hi]
  rw [hCi, eval_relabelClause] at h
  exact h

end
