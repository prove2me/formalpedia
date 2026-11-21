-- Prove2me | solution 1 for StreamSubmod.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:16:22.054745+00:00
-- url     : https://prove2.me/submissions/1f077cc1-e0a8-43d2-9f14-c63c7764a780

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1

namespace Aux_StreamSubmod_lemma_3

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

lemma run_inv {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (L : List E) :
    ∀ S : Fin p → Finset E, (∀ j, f ∅ + ((S j).card : ℝ) * θ ≤ f (S j)) →
      ∀ j, f ∅ + (((L.foldl (fun S e => (threshStep f k θ e S).1) S) j).card : ℝ) * θ ≤
        f ((L.foldl (fun S e => (threshStep f k θ e S).1) S) j) := by
  induction L with
  | nil => intro S hS; exact hS
  | cons a L ih =>
    intro S hS
    simp only [List.foldl_cons]
    exact ih _ (thresh_inv f k θ a S hS)

lemma better_ge (f : Finset E → ℝ) (A B : Finset E) :
    f A ≤ f (better f A B) ∧ f B ≤ f (better f A B) := by
  unfold better
  split_ifs with h
  · exact ⟨h.le, le_rfl⟩
  · exact ⟨le_rfl, not_lt.mp h⟩

lemma foldl_better (f : Finset E → ℝ) (L : List (Finset E)) :
    ∀ A : Finset E, f A ≤ f (L.foldl (better f) A) ∧ ∀ B ∈ L, f B ≤ f (L.foldl (better f) A) := by
  induction L with
  | nil => intro A; exact ⟨le_rfl, fun B hB => by simp at hB⟩
  | cons b L ih =>
    intro A
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := better_ge f A b
    obtain ⟨h3, h4⟩ := ih (better f A b)
    refine ⟨le_trans h1 h3, ?_⟩
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact le_trans h2 h3
    · exact h4 B hB

lemma bestOf_ge (f : Finset E → ℝ) (A : Finset E) (L : List (Finset E)) (B : Finset E)
    (hB : B ∈ L) : f B ≤ f (bestOf f (A :: L)) := by
  show f B ≤ f (L.foldl (better f) A)
  exact (foldl_better f L A).2 B hB

end Aux_StreamSubmod_lemma_3

open Aux_StreamSubmod_lemma_3 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (σ : List E)
    (hσ : IsStream σ) (hfull : ∃ i, (alg1Sets p f k α τ σ i).card = k) (ω : Ω) :
    α * τ / (1 + α) ≤ f (alg1Out p f k α τ Off σ ω) := by
  obtain ⟨i, hi⟩ := hfull
  have hinv := run_inv f k (threshold α k τ) σ (fun _ => (∅ : Finset E)) (fun j => by simp) i
  have hS : alg1Sets p f k α τ σ =
      σ.foldl (fun S e => (threshStep f k (threshold α k τ) e S).1) (fun _ => ∅) := rfl
  rw [← hS, hi] at hinv
  have hge : f (alg1Sets p f k α τ σ i) ≤ f (alg1Out p f k α τ Off σ ω) := by
    unfold alg1Out postProcess
    apply bestOf_ge
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hth : (k : ℝ) * threshold α k τ = α * τ / (1 + α) := by
    have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
    have hα' : (1 + α) ≠ 0 := by linarith
    unfold threshold
    field_simp <;> ring
  have := hf0 ∅
  linarith
