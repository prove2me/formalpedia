-- Prove2me | solution 1 for QLLL.SAT.exists_forall_clause_eval
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:54:38.450448+00:00
-- url     : https://prove2.me/submissions/7a985df4-ac7b-4581-91c5-6b24dbc96eb5

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Theorems.Thm_QLLL_SAT_card_inter_mul_card
import Theorems.Thm_QLLL_SAT_counting_clauseEvent_ge
import Theorems.Thm_QLLL_Valuation_lll_symmetric
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

theorem DependsOn.inter {S : Finset (Fin V)} {A B : Finset (Asg V)}
    (hA : DependsOn S A) (hB : DependsOn S B) : DependsOn S (A ∩ B) := by
  intro ω τ h
  simp only [Finset.mem_inter]
  rw [hA ω τ h, hB ω τ h]

theorem dependsOn_univ (S : Finset (Fin V)) :
    DependsOn S (univ : Finset (Asg V)) := fun _ _ _ => by simp

theorem dependsOn_finsetInf {S : Finset (Fin V)} {ι : Type*}
    (A : ι → Finset (Asg V)) (T : Finset ι) (hA : ∀ i ∈ T, DependsOn S (A i)) :
    DependsOn S (T.inf A) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using dependsOn_univ S
  | @insert j T' hj ih =>
    rw [Finset.inf_insert]
    exact (hA j (Finset.mem_insert_self j T')).inter
      (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

/-! ## The counting crux -/

/-! ## Independence for the counting valuation -/

theorem counting_inf {S : Finset (Fin V)} {A B : Finset (Asg V)}
    (hA : DependsOn S A) (hB : DependsOn Sᶜ B) :
    counting (Asg V) (A ⊓ B) = counting (Asg V) A * counting (Asg V) B := by
  have h := card_inter_mul_card hA hB
  have hN : (Fintype.card (Asg V) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [counting_apply, Finset.inf_eq_inter]
  field_simp
  exact_mod_cast h

/-- The classical analogue of `QLLL.QSAT.mutuallyIndepOn_of_isSupportedOn`: an
event depending on the variables in `S` is mutually independent of any family of
events depending on variables outside `S`. -/
theorem mutuallyIndepOn_of_dependsOn {S : Finset (Fin V)} {A : Finset (Asg V)}
    (hA : DependsOn S A) {ι : Type*} (Y : ι → Finset (Asg V))
    (T : Finset ι) (hY : ∀ i ∈ T, ∃ Sᵢ ⊆ Sᶜ, DependsOn Sᵢ (Y i)) :
    (counting (Asg V)).MutuallyIndepOn A Y T := by
  intro T' hT'
  refine counting_inf hA (dependsOn_finsetInf Y T' fun i hi => ?_)
  obtain ⟨Sᵢ, hsub, h⟩ := hY i (hT' hi)
  exact h.mono hsub

/-! ## Counting assignments prescribed on a set of variables -/

/-! ## Clauses -/

theorem mem_clauseVars {c : CNF.Clause (Fin V)} {i : Fin V} :
    i ∈ clauseVars c ↔ ∃ b, (i, b) ∈ c := by
  simp only [clauseVars, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨i', b⟩, hmem, rfl⟩
    exact ⟨b, hmem⟩
  · rintro ⟨b, hmem⟩
    exact ⟨(i, b), hmem, rfl⟩

theorem clause_eval_congr (c : CNF.Clause (Fin V)) {ω τ : Asg V}
    (h : ∀ i ∈ clauseVars c, ω i = τ i) :
    CNF.Clause.eval ω c = CNF.Clause.eval τ c := by
  induction c with
  | nil => simp
  | cons l c ih =>
    have hl : ω l.1 = τ l.1 := h l.1 (mem_clauseVars.mpr ⟨l.2, by simp⟩)
    have ih' : CNF.Clause.eval ω c = CNF.Clause.eval τ c := by
      refine ih fun i hi => h i ?_
      obtain ⟨b, hb⟩ := mem_clauseVars.mp hi
      exact mem_clauseVars.mpr ⟨b, List.mem_cons_of_mem _ hb⟩
    rw [CNF.Clause.eval_cons, CNF.Clause.eval_cons, hl, ih']

theorem dependsOn_clauseEvent (c : CNF.Clause (Fin V)) :
    DependsOn (clauseVars c) (clauseEvent c) := by
  intro ω τ h
  simp only [clauseEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [clause_eval_congr c h]

/-! ## The k-SAT corollary -/

theorem mem_finsetInf {ι : Type*} {X : ι → Finset (Asg V)} {T : Finset ι} {a : Asg V} :
    a ∈ T.inf X ↔ ∀ i ∈ T, a ∈ X i := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert j T' hj ih =>
    rw [Finset.inf_insert]
    simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_insert, ih]
    constructor
    · rintro ⟨h₁, h₂⟩ i (rfl | hi)
      · exact h₁
      · exact h₂ i hi
    · intro h
      exact ⟨h j (Or.inl rfl), fun i hi => h i (Or.inr hi)⟩

end QLLL.SAT


section

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable {V : ℕ}

theorem solution {V m : ℕ} (C : Fin m → CNF.Clause (Fin V))
    (k D : ℕ) (hk : 1 ≤ k) (hD1 : 1 ≤ D)
    (hvars : ∀ i, (clauseVars (C i)).card = k)
    (hdeg : ∀ v : Fin V, (univ.filter fun i => v ∈ clauseVars (C i)).card ≤ D)
    (hDk : (D : ℝ) * (Real.exp 1 * k) ≤ 2 ^ k) :
    ∃ a : Asg V, ∀ i, CNF.Clause.eval a (C i) = true := by
  classical
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  set X : Fin m → Finset (Asg V) := fun i => clauseEvent (C i) with hX
  set Γ : Fin m → Finset (Fin m) := fun i =>
    univ.filter fun j => j ≠ i ∧ (clauseVars (C i) ∩ clauseVars (C j)).Nonempty with hΓ
  -- the dependency graph
  have hdep : (counting (Asg V)).IsDependencyGraph X Γ := by
    intro i
    refine mutuallyIndepOn_of_dependsOn (dependsOn_clauseEvent (C i)) X _ ?_
    intro j hj
    refine ⟨clauseVars (C j), ?_, dependsOn_clauseEvent (C j)⟩
    rw [Finset.mem_erase, Finset.mem_sdiff] at hj
    obtain ⟨hji, -, hjΓ⟩ := hj
    simp only [hΓ, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hjΓ
    have hempty := hjΓ hji
    intro v hv
    rw [Finset.mem_compl]
    intro hvi
    exact hempty ⟨v, Finset.mem_inter.mpr ⟨hvi, hv⟩⟩
  -- the degree bound
  have hdegΓ : ∀ i, (Γ i).card ≤ k * D' := by
    intro i
    have hsub : Γ i ⊆ (clauseVars (C i)).biUnion
        fun v => (univ.filter fun j : Fin m => v ∈ clauseVars (C j)).erase i := by
      intro j hj
      simp only [hΓ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨hji, v, hv⟩ := hj
      rw [Finset.mem_inter] at hv
      exact Finset.mem_biUnion.mpr ⟨v, hv.1, Finset.mem_erase.mpr ⟨hji,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.2⟩⟩⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    calc ∑ v ∈ clauseVars (C i),
            ((univ.filter fun j : Fin m => v ∈ clauseVars (C j)).erase i).card
        ≤ ∑ _v ∈ clauseVars (C i), D' := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hi : i ∈ univ.filter fun j : Fin m => v ∈ clauseVars (C j) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
          rw [Finset.card_erase_of_mem hi]
          have := hdeg v
          omega
      _ = (clauseVars (C i)).card * D' := by rw [Finset.sum_const, smul_eq_mul]
      _ = k * D' := by rw [hvars i]
  -- each clause is satisfied by all but a `2 ^ (-k)` fraction
  have hXge : ∀ i, 1 - 1 / 2 ^ k ≤ counting (Asg V) (X i) := fun i =>
    counting_clauseEvent_ge (hvars i)
  -- the arithmetic hypothesis of the symmetric local lemma
  have hkR : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have hp : (1 / (2:ℝ) ^ k) * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_one h2k]
    push_cast at hDk ⊢
    nlinarith [hDk, mul_nonneg he.le (by linarith : (0:ℝ) ≤ (k:ℝ) - 1)]
  have hcount := Valuation.lll_symmetric (counting (Asg V)) hdep hdegΓ hXge hp
  -- a nonempty intersection is a satisfying assignment
  have hcard : 0 < (univ.inf X).card := by
    rcases Nat.eq_zero_or_pos (univ.inf X).card with h0 | hpos
    · rw [counting_apply, h0] at hcount
      simp at hcount
    · exact hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hcard
  refine ⟨a, fun i => ?_⟩
  have := mem_finsetInf.mp ha i (Finset.mem_univ i)
  simpa [hX, clauseEvent] using this

end
