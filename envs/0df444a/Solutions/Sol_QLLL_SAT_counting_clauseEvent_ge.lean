-- Prove2me | solution 1 for QLLL.SAT.counting_clauseEvent_ge
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:50:29.649921+00:00
-- url     : https://prove2.me/submissions/a1f9b84a-e689-42db-b197-a801adaf447e

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Theorems.Thm_QLLL_SAT_card_inter_mul_card
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

@[simp] theorem counting_apply (A : Finset Ω) :
    counting Ω A = (A.card : ℝ) / (Fintype.card Ω : ℝ) := rfl

/-! ## Events depending on a set of variables -/

variable {V : ℕ}

theorem DependsOn.mono {S T : Finset (Fin V)} {A : Finset (Asg V)}
    (hST : S ⊆ T) (hA : DependsOn S A) : DependsOn T A :=
  fun ω τ h => hA ω τ fun i hi => h i (hST hi)

/-! ## The counting crux -/

/-! ## Independence for the counting valuation -/

/-! ## Counting assignments prescribed on a set of variables -/

theorem dependsOn_fixedOn (S : Finset (Fin V)) (g : Asg V) :
    DependsOn S (fixedOn S g) := by
  intro ω τ h
  simp only [fixedOn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hω i hi; rw [← h i hi]; exact hω i hi
  · intro hτ i hi; rw [h i hi]; exact hτ i hi

theorem fixedOn_insert (j : Fin V) (S : Finset (Fin V)) (g : Asg V) :
    fixedOn (insert j S) g = fixedOn S g ∩ fixedOn {j} g := by
  ext a
  simp only [fixedOn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inr hi), fun i hi => h i (Or.inl hi)⟩
  · rintro ⟨h₁, h₂⟩ i (rfl | hi)
    · exact h₂ i rfl
    · exact h₁ i hi

/-- Exactly half the assignments agree with `g` at a given variable. -/
theorem card_fixedOn_singleton_mul (j : Fin V) (g : Asg V) :
    (fixedOn {j} g).card * 2 = Fintype.card (Asg V) := by
  classical
  have key : ((fixedOn {j} g) ×ˢ (univ : Finset Bool)).card
      = (univ : Finset (Asg V)).card := by
    refine Finset.card_bij'
      (fun (q : Asg V × Bool) _ => Function.update q.1 j q.2)
      (fun (a : Asg V) _ => (Function.update a j (g j), a j)) ?_ ?_ ?_ ?_
    · intro q _; exact Finset.mem_univ _
    · intro a _
      simp only [Finset.mem_product, Finset.mem_univ, and_true, fixedOn,
        Finset.mem_filter, true_and, Finset.mem_singleton]
      intro i hi
      subst hi
      simp
    · rintro ⟨a, v⟩ hq
      simp only [Finset.mem_product, Finset.mem_univ, and_true, fixedOn,
        Finset.mem_filter, true_and, Finset.mem_singleton] at hq
      have haj : a j = g j := hq j rfl
      simp only [Prod.mk.injEq, Function.update_idem, Function.update_self]
      exact ⟨by rw [← haj, Function.update_eq_self], trivial⟩
    · intro a _
      simp [Function.update_idem]
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Finset.card_univ] at key
  exact key

theorem card_fixedOn_mul (S : Finset (Fin V)) (g : Asg V) :
    (fixedOn S g).card * 2 ^ S.card = Fintype.card (Asg V) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fixedOn]
  | @insert j S hj ih =>
    have hN : 0 < Fintype.card (Asg V) := Fintype.card_pos
    have hsub : ({j} : Finset (Fin V)) ⊆ Sᶜ :=
      Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hj)
    have hcrux := card_inter_mul_card (dependsOn_fixedOn S g)
      ((dependsOn_fixedOn {j} g).mono hsub)
    rw [← fixedOn_insert] at hcrux
    have hhalf := card_fixedOn_singleton_mul j g
    have hstep : (fixedOn (insert j S) g).card * 2 = (fixedOn S g).card := by
      have h2 : (fixedOn (insert j S) g).card * 2 * Fintype.card (Asg V)
          = (fixedOn S g).card * Fintype.card (Asg V) := by
        calc (fixedOn (insert j S) g).card * 2 * Fintype.card (Asg V)
            = ((fixedOn (insert j S) g).card * Fintype.card (Asg V)) * 2 := by ring
          _ = ((fixedOn S g).card * (fixedOn {j} g).card) * 2 := by rw [hcrux]
          _ = (fixedOn S g).card * ((fixedOn {j} g).card * 2) := by ring
          _ = (fixedOn S g).card * Fintype.card (Asg V) := by rw [hhalf]
      exact Nat.eq_of_mul_eq_mul_right hN h2
    rw [Finset.card_insert_of_notMem hj, pow_succ]
    calc (fixedOn (insert j S) g).card * (2 ^ S.card * 2)
        = ((fixedOn (insert j S) g).card * 2) * 2 ^ S.card := by ring
      _ = (fixedOn S g).card * 2 ^ S.card := by rw [hstep]
      _ = Fintype.card (Asg V) := ih

/-! ## Clauses -/

theorem mem_clauseVars {c : CNF.Clause (Fin V)} {i : Fin V} :
    i ∈ clauseVars c ↔ ∃ b, (i, b) ∈ c := by
  simp only [clauseVars, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨i', b⟩, hmem, rfl⟩
    exact ⟨b, hmem⟩
  · rintro ⟨b, hmem⟩
    exact ⟨(i, b), hmem, rfl⟩

theorem eval_eq_true_of_mem {c : CNF.Clause (Fin V)} {i : Fin V} {b : Bool}
    (hb : (i, b) ∈ c) {x : Asg V} (hx : x i = b) : CNF.Clause.eval x c = true := by
  simp only [CNF.Clause.eval, List.any_eq_true]
  exact ⟨(i, b), hb, by simp [hx]⟩

/-! ## The k-SAT corollary -/

end QLLL.SAT


section

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable {V : ℕ}

theorem solution {c : CNF.Clause (Fin V)} {k : ℕ}
    (hk : (clauseVars c).card = k) :
    1 - 1 / 2 ^ k ≤ counting (Asg V) (clauseEvent c) := by
  classical
  have hNpos : 0 < Fintype.card (Asg V) := Fintype.card_pos
  set F := univ.filter fun a : Asg V => ¬ (CNF.Clause.eval a c = true) with hFdef
  have hpart : (clauseEvent c).card + F.card = Fintype.card (Asg V) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Asg V))) (p := fun a : Asg V => CNF.Clause.eval a c = true)
    simpa [clauseEvent, hFdef, Finset.card_univ] using h
  have hFbound : F.card * 2 ^ k ≤ Fintype.card (Asg V) := by
    rcases F.eq_empty_or_nonempty with hFe | ⟨a₀, ha₀⟩
    · simp [hFe]
    · have hsub : F ⊆ fixedOn (clauseVars c) a₀ := by
        intro a ha
        simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and] at ha ha₀
        simp only [fixedOn, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        obtain ⟨b, hb⟩ := mem_clauseVars.mp hi
        have h1 : a i ≠ b := fun hEq => ha (eval_eq_true_of_mem hb hEq)
        have h2 : a₀ i ≠ b := fun hEq => ha₀ (eval_eq_true_of_mem hb hEq)
        revert h1 h2
        cases a i <;> cases a₀ i <;> cases b <;> simp
      calc F.card * 2 ^ k
          ≤ (fixedOn (clauseVars c) a₀).card * 2 ^ k :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ = Fintype.card (Asg V) := by rw [← hk]; exact card_fixedOn_mul _ _
  have hNR : (0:ℝ) < (Fintype.card (Asg V) : ℝ) := by exact_mod_cast hNpos
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  simp only [counting_apply]
  rw [le_div_iff₀ hNR]
  have hFR : (F.card : ℝ) * 2 ^ k ≤ (Fintype.card (Asg V) : ℝ) := by exact_mod_cast hFbound
  have hkey : (F.card : ℝ) ≤ (Fintype.card (Asg V) : ℝ) / 2 ^ k :=
    (le_div_iff₀ h2k).mpr hFR
  have hEq : ((clauseEvent c).card : ℝ)
      = (Fintype.card (Asg V) : ℝ) - (F.card : ℝ) := by
    have := hpart
    push_cast [← this]
    ring
  have hexp : (1 - 1 / (2:ℝ) ^ k) * (Fintype.card (Asg V) : ℝ)
      = (Fintype.card (Asg V) : ℝ) - (Fintype.card (Asg V) : ℝ) / 2 ^ k := by
    field_simp
  rw [hEq, hexp]
  linarith

end
