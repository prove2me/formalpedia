-- Prove2me | solution 1 for QLLL.SAT.exists_assignment_forall
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T18:02:04.380194+00:00
-- url     : https://prove2.me/submissions/242f8827-9cd9-4652-856f-3bfd6074d7d3

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Definitions.Def_QLLL_Classical_InfiniteKSAT
import Theorems.Thm_QLLL_SAT_exists_assignment_of_finset
import Mathlib
import Std.Sat.CNF

-- inline helpers from QuantumLocalLemma.Classical.Compactness
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# Compactness for boolean assignments

The infinite Lovász Local Lemma does not come from the finite one by a
measure-theoretic limit. The valuation axioms used in `QuantumLocalLemma.LocalLemma.Basic` are
finitely additive, and finite additivity does not give continuity from above:
a finitely additive probability on `ℕ` with `μ(finite) = 0` has
`μ({n, n+1, …}) = 1` for every `n` while the intersection is empty. Even with
countable additivity the quantitative bound `∏ (1 - yᵢ)` is usually `0`, hence
vacuous, and for uncountably many events continuity fails outright.

What does work is compactness, and it is insensitive to cardinality. The results
here are stated for arbitrary types `V` and `ι`: no `Countable`, no `Fintype`.
`{0,1}^V` is compact by Tychonoff for any `V`, a constraint reading finitely many
variables is clopen, and the finite intersection property does the rest. The
finiteness that matters is that `Bool` is finite and that each constraint reads
finitely many variables, not that there are countably many of either.
-/

open Set Topology

namespace QLLL.Compactness

/-- A set of boolean assignments determined by the values on a finite set `S` of
variables is closed in the product topology. -/
theorem isClosed_of_dependsOn {V : Type*} (S : Finset V) (G : Set (V → Bool))
    (h : ∀ ω τ : V → Bool, (∀ v ∈ S, ω v = τ v) → (ω ∈ G ↔ τ ∈ G)) :
    IsClosed G := by
  set f : (V → Bool) → ({v // v ∈ S} → Bool) := fun ω v => ω v.1 with hf
  have hcont : Continuous f := continuous_pi fun v => continuous_apply v.1
  have hpre : G = f ⁻¹' (f '' G) := by
    apply Set.Subset.antisymm
    · exact Set.subset_preimage_image f G
    · rintro ω ⟨τ, hτG, hτ⟩
      refine (h ω τ ?_).mpr hτG
      intro v hv
      exact (congrFun hτ ⟨v, hv⟩).symm
  rw [hpre]
  exact (isClosed_discrete _).preimage hcont

/-- **Compactness principle.** If every finite subfamily of a family of closed
sets of assignments has a common point, so does the whole family.

Note the absence of any hypothesis on the cardinality of `ι`, and that `ι` may
be empty. -/
theorem exists_mem_iInter_of_finite {V ι : Type*} (G : ι → Set (V → Bool))
    (hclosed : ∀ i, IsClosed (G i))
    (hfin : ∀ T : Finset ι, ∃ ω, ∀ i ∈ T, ω ∈ G i) :
    ∃ ω : V → Bool, ∀ i, ω ∈ G i := by
  have key : (Set.univ ∩ ⋂ i, G i).Nonempty := by
    refine isCompact_univ.inter_iInter_nonempty G hclosed fun T => ?_
    obtain ⟨ω, hω⟩ := hfin T
    exact ⟨ω, Set.mem_univ _, Set.mem_iInter₂.mpr hω⟩
  obtain ⟨ω, -, hω⟩ := key
  exact ⟨ω, Set.mem_iInter.mp hω⟩

/-- **Propositional compactness.** If every finite subfamily of a family of
finitely-determined constraints is satisfiable, the whole family is. -/
theorem exists_forall_of_forall_finite {V ι : Type*} (G : ι → Set (V → Bool))
    (S : ι → Finset V)
    (hdep : ∀ i, ∀ ω τ : V → Bool, (∀ v ∈ S i, ω v = τ v) → (ω ∈ G i ↔ τ ∈ G i))
    (hfin : ∀ T : Finset ι, ∃ ω, ∀ i ∈ T, ω ∈ G i) :
    ∃ ω : V → Bool, ∀ i, ω ∈ G i :=
  exists_mem_iInter_of_finite G (fun i => isClosed_of_dependsOn (S i) (G i) (hdep i)) hfin

end QLLL.Compactness


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

/-- A clause reads only its own variables. This is what makes the set of
assignments satisfying it closed in the product topology. -/
theorem clause_eval_congr' {V : Type*} [DecidableEq V] (c : CNF.Clause V)
    {ω τ : V → Bool} (h : ∀ v ∈ clauseVars' c, ω v = τ v) :
    CNF.Clause.eval ω c = CNF.Clause.eval τ c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    have hl : ω l.1 = τ l.1 := h l.1 (mem_clauseVars'.mpr ⟨l.2, by simp⟩)
    have ih' : CNF.Clause.eval ω c = CNF.Clause.eval τ c := by
      refine ih fun v hv => h v ?_
      obtain ⟨b, hb⟩ := mem_clauseVars'.mp hv
      exact mem_clauseVars'.mpr ⟨b, List.mem_cons_of_mem _ hb⟩
    rw [CNF.Clause.eval_cons, CNF.Clause.eval_cons, hl, ih']

/-! ## The finite theorem over arbitrary types -/

/-! ## The infinite theorem -/

end QLLL.SAT


section

open QLLL
open QLLL.SAT
open Finset Std.Sat

theorem solution {V ι : Type*} [DecidableEq V]
    (C : ι → CNF.Clause V) (k D : ℕ) (hk : 1 ≤ k) (hD1 : 1 ≤ D)
    (hvars : ∀ i, (clauseVars' (C i)).card = k)
    (hdeg : ∀ (v : V) (T : Finset ι),
      (T.filter fun i => v ∈ clauseVars' (C i)).card ≤ D)
    (hDk : (D : ℝ) * (Real.exp 1 * k) ≤ 2 ^ k) :
    ∃ a : V → Bool, ∀ i, CNF.Clause.eval a (C i) = true := by
  classical
  have h := QLLL.Compactness.exists_forall_of_forall_finite
    (V := V) (ι := ι)
    (fun i => {a : V → Bool | CNF.Clause.eval a (C i) = true})
    (fun i => clauseVars' (C i))
    (fun i ω τ hagree => by
      simp only [Set.mem_ofPred_eq]
      rw [clause_eval_congr' (C i) hagree])
    (fun T => by
      obtain ⟨a, ha⟩ :=
        exists_assignment_of_finset C T k D hk hD1 (fun i _ => hvars i)
          (fun v => hdeg v T) hDk
      exact ⟨a, fun i hi => ha i hi⟩)
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun i => ha i⟩

end
