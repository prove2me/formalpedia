-- Prove2me | solution 1 for StreamSubmod.observation_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:25:28.454187+00:00
-- url     : https://prove2.me/submissions/6d5af7c5-4684-4b7d-8284-b850e5097aaf

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Algorithm2

namespace Aux_StreamSubmod_observation_11

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

lemma thresh_card_le {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (i : Fin p) : ((threshStep f k θ e S).1 i).card ≤ (S i).card + 1 := by
  unfold threshStep
  rcases hs : scan f k θ e S (List.finRange p) with ⟨o, n⟩
  cases o with
  | none => dsimp only; omega
  | some j =>
    dsimp only
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      exact Finset.card_insert_le e (S i)
    · rw [Function.update_of_ne hij]
      omega

lemma card_step {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (c : Prop) [Decidable c]
    (K : Fin p → Finset E) (i : Fin p) :
    ((if c then (threshStep f k θ e K).1 else fun _ => (∅ : Finset E)) i).card ≤
      (K i).card + 1 := by
  split_ifs
  · exact thresh_card_le f k θ e K i
  · simp

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

lemma main {p : ℕ} (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S) (k : ℕ) (hk : 1 ≤ k) (α : ℝ)
    (hα0 : 0 < α) (ε' : ℝ) (hε0 : 0 < ε') (L : List E) (h : ℤ) (i : Fin p) :
    (((alg2Run p f k α ε' L).sets h i).card : ℝ) ≤
      (alg2Run p f k α ε' L).m * (k : ℝ) / (α / (1 + α) * (1 + ε') ^ h) + 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hq0 : (0 : ℝ) < 1 + ε' := by linarith
  have hc0 : 0 < α / (1 + α) := div_pos hα0 (by linarith)
  have hθ : 0 < threshold α k ((1 + ε') ^ h) := by
    unfold threshold
    exact div_pos (mul_pos hc0 (zpow_pos hq0 h)) hkpos
  have hθeq : ∀ m : ℝ, m / threshold α k ((1 + ε') ^ h) =
      m * (k : ℝ) / (α / (1 + α) * (1 + ε') ^ h) := by
    intro m
    unfold threshold
    rw [div_div_eq_mul_div]
  rcases List.eq_nil_or_concat L with rfl | ⟨L', e, rfl⟩
  · have h0 : ((alg2Run p f k α ε' []).sets h i) = ∅ := rfl
    have hm : (alg2Run p f k α ε' []).m = f ∅ := rfl
    rw [h0, hm]
    have : 0 ≤ f ∅ * (k : ℝ) / (α / (1 + α) * (1 + ε') ^ h) :=
      div_nonneg (mul_nonneg (hf0 ∅) hkpos.le) (mul_pos hc0 (zpow_pos hq0 h)).le
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hrun : alg2Run p f k α ε' (L'.concat e) =
        (alg2Step p f k α ε' e (alg2Run p f k α ε' L')).1 := by
      unfold alg2Run
      rw [List.concat_eq_append, List.foldl_append]
      rfl
    rw [hrun]
    obtain ⟨st, hst⟩ : ∃ st, st = alg2Run p f k α ε' L' := ⟨_, rfl⟩
    rw [← hst]
    have hI : Inv f k α ε' st := by
      rw [hst]
      exact run_inv f k α ε' L' _ (fun h i => by simp [alg2Init])
    obtain ⟨M', hM'⟩ : ∃ M', M' = (alg2Guesses k α ε' st ×ˢ (Finset.univ : Finset (Fin p))).fold
        max (f {e}) (fun x => f (st.sets x.1 x.2)) := ⟨_, rfl⟩
    have hmeq : (alg2Step p f k α ε' e st).1.m = if st.m < M' then M' else st.m := by
      rw [hM']; rfl
    have hM'ge : f {e} ≤ M' := by
      rw [hM', Finset.le_fold_max]
      exact Or.inl le_rfl
    have hm1 : M' ≤ (alg2Step p f k α ε' e st).1.m := by
      rw [hmeq]; split_ifs <;> linarith
    have hcard : ((alg2Step p f k α ε' e st).1.sets h i).card ≤
        ((if h ∈ alg2Guesses k α ε' st then st.sets h else fun _ => (∅ : Finset E)) i).card + 1 := by
      dsimp only [alg2Step]
      exact card_step f k _ e _ _ i
    obtain ⟨X, hX⟩ : ∃ X : ℕ, X =
        ((if h ∈ alg2Guesses k α ε' st then st.sets h else fun _ => (∅ : Finset E)) i).card :=
      ⟨_, rfl⟩
    rw [← hX] at hcard
    have hXθ : (X : ℝ) * threshold α k ((1 + ε') ^ h) ≤ (alg2Step p f k α ε' e st).1.m := by
      by_cases hT : h ∈ alg2Guesses k α ε' st
      · rw [if_pos hT] at hX
        have h1 := hI h i
        have h2 : f (st.sets h i) ≤ M' := by
          rw [hM', Finset.le_fold_max]
          refine Or.inr ⟨(h, i), Finset.mem_product.mpr ⟨hT, Finset.mem_univ _⟩, le_rfl⟩
        rw [hX]
        have := hf0 ∅
        linarith
      · rw [if_neg hT] at hX
        simp only [Finset.card_empty] at hX
        rw [hX]
        have := hf0 {e}
        simp only [Nat.cast_zero, zero_mul]
        linarith
    have hX2 : (X : ℝ) ≤ (alg2Step p f k α ε' e st).1.m / threshold α k ((1 + ε') ^ h) :=
      (le_div_iff₀ hθ).mpr hXθ
    rw [hθeq] at hX2
    have hcard' : (((alg2Step p f k α ε' e st).1.sets h i).card : ℝ) ≤ (X : ℝ) + 1 := by
      exact_mod_cast hcard
    linarith

end Aux_StreamSubmod_observation_11

open Aux_StreamSubmod_observation_11 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (ε' : ℝ) (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ) (hp : 1 ≤ p) (σ : List E)
    (hσ : IsStream σ) (L : List E) (hL : L <+: σ) :
    let st := alg2Run p f k α ε' L
    let c := α / (1 + α)
    ∀ h ∈ alg2Guesses k α ε' st, ∀ i,
      ((st.sets h i).card : ℝ) ≤ st.m * (k : ℝ) / (c * (1 + ε') ^ h) + 1 := by
  intro st c h _ i
  exact main f hf0 k hk α hα0 ε' hε0 L h i
