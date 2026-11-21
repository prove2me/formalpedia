-- Prove2me | solution 1 for StreamSubmod.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:21:10.320184+00:00
-- url     : https://prove2.me/submissions/10f651f9-c9ed-4b7f-8dfe-3e7fbc756f91

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Algorithm2

namespace Aux_StreamSubmod_lemma_10

open StreamSubmod NonmonotoneSubmod.Shared

variable {E : Type} [DecidableEq E]

lemma scan_some {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (i : Fin p) : ∀ l : List (Fin p), (scan f k θ e S l).1 = some i →
      θ ≤ marginal f e (S i) := by
  intro l
  induction l with
  | nil => intro h; simp [scan] at h
  | cons j l ih =>
    intro h
    simp only [scan] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h
      subst h
      exact h2
    · exact ih h
    · exact ih h

lemma thresh_inv {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (hS : ∀ j, f ∅ + ((S j).card : ℝ) * θ ≤ f (S j)) (i : Fin p) :
    f ∅ + (((threshStep f k θ e S).1 i).card : ℝ) * θ ≤ f ((threshStep f k θ e S).1 i) := by
  unfold threshStep
  rcases hs : scan f k θ e S (List.finRange p) with ⟨o, n⟩
  cases o with
  | none => exact hS i
  | some j =>
    have hj := scan_some f k θ e S j (List.finRange p) (by simp [hs])
    dsimp only
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      unfold marginal at hj
      by_cases he : e ∈ S i
      · rw [Finset.insert_eq_of_mem he]
        exact hS i
      · rw [Finset.card_insert_of_notMem he]
        have := hS i
        push_cast
        linarith
    · rw [Function.update_of_ne hij]
      exact hS i

lemma ite_inv {p : ℕ} (f : Finset E → ℝ) (θ : ℝ) (c : Prop) [Decidable c]
    (F : Fin p → Finset E) (hF : ∀ j, f ∅ + ((F j).card : ℝ) * θ ≤ f (F j)) (i : Fin p) :
    f ∅ + (((if c then F else fun _ => (∅ : Finset E)) i).card : ℝ) * θ ≤
      f ((if c then F else fun _ => (∅ : Finset E)) i) := by
  split_ifs
  · exact hF i
  · simp

abbrev Inv {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (st : Alg2State E p) : Prop :=
  ∀ h i, f ∅ + ((st.sets h i).card : ℝ) * threshold α k ((1 + ε') ^ h) ≤ f (st.sets h i)

lemma step_inv {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (e : E)
    (st : Alg2State E p) (hI : Inv f k α ε' st) :
    Inv f k α ε' (alg2Step p f k α ε' e st).1 := by
  intro h i
  dsimp only [alg2Step]
  exact ite_inv f _ _ _ (thresh_inv f k _ e _ (fun j => ite_inv f _ _ _ (hI h) j)) i

lemma run_inv {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (L : List E) :
    ∀ st : Alg2State E p, Inv f k α ε' st →
      Inv f k α ε' (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st) := by
  induction L with
  | nil => intro st hI; exact hI
  | cons a L ih =>
    intro st hI
    simp only [List.foldl_cons]
    exact ih _ (step_inv f k α ε' a st hI)

end Aux_StreamSubmod_lemma_10

open Aux_StreamSubmod_lemma_10 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (ε' : ℝ)
    (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ) (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ) (L : List E)
    (hL : L <+: σ) :
    let st := alg2Run p f k α ε' L
    ∀ h ∈ alg2Guesses k α ε' st, ∀ i,
      α * (1 + ε') ^ h * ((st.sets h i).card : ℝ) / ((1 + α) * (k : ℝ)) ≤ f (st.sets h i) := by
  intro st h _ i
  have hinit : Inv f k α ε' (alg2Init p f : Alg2State E p) := by
    intro h i
    simp [alg2Init]
  have hI : Inv f k α ε' st := run_inv f k α ε' L _ hinit
  have h1 := hI h i
  have h2 := hf0 ∅
  have heq : α * (1 + ε') ^ h * ((st.sets h i).card : ℝ) / ((1 + α) * (k : ℝ)) =
      ((st.sets h i).card : ℝ) * threshold α k ((1 + ε') ^ h) := by
    rw [div_eq_mul_inv, mul_inv]
    unfold threshold
    ring
  rw [heq]
  linarith
