-- Prove2me | solution 1 for QLLL.SAT.card_inter_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:48:11.664979+00:00
-- url     : https://prove2.me/submissions/c7b9fb95-bf36-4f3a-b75e-d2a10fccc73e

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Mathlib
import Std.Sat.CNF

-- inline helpers from QuantumLocalLemma.Classical.KSAT
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The classical Lovász Local Lemma and k-SAT

Towards Corollary 2 of arXiv:0911.1696: a `k`-SAT formula in which every
variable appears in at most `2 ^ k / (e * k)` clauses is satisfiable.

This is the classical shadow of the `k`-QSAT development in `QuantumLocalLemma.Quantum.KQSAT.Basic`.
The two share their whole structure; the only difference is the independence
step, which here is finite counting rather than tensor algebra.

Satisfiability is *not* defined here. We use `Std.Sat.CNF` from the Lean core
library, the same notion `bv_decide` is verified against, so that the statement
proved is the standard one rather than one shaped to fit the proof.

Instantiating `QLLL.Valuation` at `Finset Ω` with `R A = |A| / |Ω|` also yields
the classical asymmetric local lemma of Erdős and Lovász, which Mathlib does
not currently contain in any form.
-/

namespace QLLL.SAT

open Finset Std.Sat

/-! ## The counting valuation -/

variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-! ## Events depending on a set of variables -/

variable {V : ℕ}

/-! ## The counting crux -/

@[simp] theorem merge_mem {S : Finset (Fin V)} {ω τ : Asg V} {i : Fin V} (hi : i ∈ S) :
    merge S ω τ i = ω i := if_pos hi

@[simp] theorem merge_notMem {S : Finset (Fin V)} {ω τ : Asg V} {i : Fin V} (hi : i ∉ S) :
    merge S ω τ i = τ i := if_neg hi

theorem merge_merge (S : Finset (Fin V)) (ω τ : Asg V) :
    merge S (merge S ω τ) (merge S τ ω) = ω := by
  funext i
  by_cases hi : i ∈ S <;> simp [merge, hi]

theorem DependsOn.merge_left {S : Finset (Fin V)} {A : Finset (Asg V)}
    (hA : DependsOn S A) (ω τ : Asg V) : merge S ω τ ∈ A ↔ ω ∈ A :=
  (hA ω (merge S ω τ) fun _ hi => (merge_mem hi).symm).symm

theorem DependsOn.merge_right {S : Finset (Fin V)} {B : Finset (Asg V)}
    (hB : DependsOn Sᶜ B) (ω τ : Asg V) : merge S ω τ ∈ B ↔ τ ∈ B := by
  refine (hB τ (merge S ω τ) fun i hi => ?_).symm
  rw [Finset.mem_compl] at hi
  exact (merge_notMem hi).symm

/-! ## Independence for the counting valuation -/

/-! ## Counting assignments prescribed on a set of variables -/

/-! ## Clauses -/

/-! ## The k-SAT corollary -/

end QLLL.SAT


section

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable {V : ℕ}

theorem solution {S : Finset (Fin V)} {A B : Finset (Asg V)}
    (hA : DependsOn S A) (hB : DependsOn Sᶜ B) :
    (A ∩ B).card * Fintype.card (Asg V) = A.card * B.card := by
  classical
  have key : ((A ∩ B) ×ˢ (univ : Finset (Asg V))).card = (A ×ˢ B).card := by
    refine Finset.card_bij'
      (fun (p : Asg V × Asg V) _ => (merge S p.1 p.2, merge S p.2 p.1))
      (fun (q : Asg V × Asg V) _ => (merge S q.1 q.2, merge S q.2 q.1)) ?_ ?_ ?_ ?_
    · rintro ⟨ω, τ⟩ h
      simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_univ, and_true] at h ⊢
      exact ⟨(hA.merge_left ω τ).mpr h.1, (hB.merge_right τ ω).mpr h.2⟩
    · rintro ⟨x, y⟩ h
      simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_univ, and_true] at h ⊢
      exact ⟨(hA.merge_left x y).mpr h.1, (hB.merge_right x y).mpr h.2⟩
    · rintro ⟨ω, τ⟩ _
      simp [merge_merge]
    · rintro ⟨x, y⟩ _
      simp [merge_merge]
  simpa [Finset.card_product, Finset.card_univ] using key

end
