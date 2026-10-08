-- Prove2me | solution 1 for WeightedMajority.Anomalies.first_stage
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:58:35.380652+00:00
-- url     : https://prove2.me/submissions/4daf2505-c56c-40d6-b537-ecd2651cb230

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Anomalies_Opt
open UnderstandingML

private theorem subtree {X : Type*} {F : Set (X → Bool)} {n : ℕ}
    {v : List Bool → X} (hv : ShattersTree F (n+1) v) (b : Bool) :
    ShattersTree {f ∈ F | f (v []) = b} n (fun p => v (b :: p)) := by
  intro y
  obtain ⟨f, hf, hpath⟩ := hv (Fin.cons b y)
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · simpa using hpath 0
  · intro t
    have h := hpath t.succ
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ] at h
    exact h

private theorem first {X : Type*} (F : Set (X → Bool)) (A : OnlineAlg X Bool)
    (n : ℕ) (htree : ∃ v : List Bool → X, ShattersTree F (n+1) v) :
    ∃ S : Fin n → X × Bool,
      (∀ t : Fin n, A (history S t) (S t).1 ≠ (S t).2) ∧
      ∃ f₁ ∈ F, ∃ f₂ ∈ F, ∃ x : X,
        (∀ t : Fin n, f₁ (S t).1 = (S t).2) ∧
        (∀ t : Fin n, f₂ (S t).1 = (S t).2) ∧ f₁ x ≠ f₂ x := by
  induction n generalizing F A with
  | zero =>
    obtain ⟨v, hv⟩ := htree
    obtain ⟨f, hf, hfalse⟩ := hv (fun _ => false)
    obtain ⟨g, hg, htrue⟩ := hv (fun _ => true)
    refine ⟨Fin.elim0, (by intro t; exact Fin.elim0 t), f, hf, g, hg, v [],
      (by intro t; exact Fin.elim0 t), (by intro t; exact Fin.elim0 t), ?_⟩
    have h0 : f (v []) = false := by simpa using hfalse 0
    have h1 : g (v []) = true := by simpa using htrue 0
    rw [h0, h1]
    decide
  | succ n ih =>
    obtain ⟨v, hv⟩ := htree
    let x := v []
    let b := !(A [] x)
    let F' : Set (X → Bool) := {f ∈ F | f x = b}
    let A' : OnlineAlg X Bool := fun h z => A ((x,b) :: h) z
    obtain ⟨S, hS, f, hf, g, hg, z, hfc, hgc, hfg⟩ :=
      ih F' A' ⟨fun p => v (b :: p), subtree hv b⟩
    refine ⟨Fin.cons (x,b) S, ?_, f, hf.1, g, hg.1, z, ?_, ?_, hfg⟩
    · intro t
      refine Fin.cases ?_ (fun i => ?_) t
      · simp [history, List.ofFn_succ, b]
      · simpa [history, List.ofFn_succ, A'] using hS i
    · intro t
      exact Fin.cases hf.2 hfc t
    · intro t
      exact Fin.cases hg.2 hgc t

theorem solution {X : Type*} (F : Set (X → Bool)) (A : OnlineAlg X Bool) (k : ℕ)
    (hk : 1 ≤ k) (htree : ∃ v : List Bool → X, ShattersTree F k v) :
    ∃ S : Fin (k - 1) → X × Bool,
      (∀ t : Fin (k - 1), A (history S t) (S t).1 ≠ (S t).2) ∧
      ∃ f₁ ∈ F, ∃ f₂ ∈ F, ∃ x : X,
        (∀ t : Fin (k - 1), f₁ (S t).1 = (S t).2) ∧
        (∀ t : Fin (k - 1), f₂ (S t).1 = (S t).2) ∧
        f₁ x ≠ f₂ x := by
  apply first
  simpa [Nat.sub_add_cancel hk] using htree

#print axioms solution
