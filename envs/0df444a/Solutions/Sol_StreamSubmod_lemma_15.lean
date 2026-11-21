-- Prove2me | solution 1 for StreamSubmod.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:29:45.319033+00:00
-- url     : https://prove2.me/submissions/824f6e18-0754-40ff-92d7-fcbddb48864a

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1
import Definitions.Def_StreamSubmod_Algorithm2

namespace Aux_StreamSubmod_lemma_15

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

lemma thresh_empty {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E)
    (he : marginal f e ∅ < θ) :
    (threshStep f k θ e (fun _ : Fin p => (∅ : Finset E))).1 = fun _ => ∅ := by
  unfold threshStep
  rcases hs : scan f k θ e (fun _ : Fin p => (∅ : Finset E)) (List.finRange p) with ⟨o, n⟩
  cases o with
  | none => rfl
  | some j =>
    have hj := scan_some f k θ e (fun _ : Fin p => (∅ : Finset E)) j (List.finRange p)
      (by simp [hs])
    exact absurd hj (not_le.mpr he)

lemma alg1_empty {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (L : List E)
    (hL : ∀ e ∈ L, marginal f e ∅ < θ) :
    L.foldl (fun S e => (threshStep f k θ e S).1) (fun _ : Fin p => (∅ : Finset E)) =
      fun _ => ∅ := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [thresh_empty f k θ a (hL a (List.mem_cons_self))]
    exact ih (fun e he => hL e (List.mem_cons_of_mem a he))

lemma step_m {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (e : E) (st : Alg2State E p) :
    st.m ≤ (alg2Step p f k α ε' e st).1.m ∧ f {e} ≤ (alg2Step p f k α ε' e st).1.m := by
  obtain ⟨M', hM'⟩ : ∃ M', M' = (alg2Guesses k α ε' st ×ˢ (Finset.univ : Finset (Fin p))).fold
      max (f {e}) (fun x => f (st.sets x.1 x.2)) := ⟨_, rfl⟩
  have hmeq : (alg2Step p f k α ε' e st).1.m = if st.m < M' then M' else st.m := by
    rw [hM']; rfl
  have hM'ge : f {e} ≤ M' := by
    rw [hM', Finset.le_fold_max]
    exact Or.inl le_rfl
  rw [hmeq]
  constructor <;> split_ifs <;> linarith

lemma run_m {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (L : List E) :
    ∀ st : Alg2State E p,
      st.m ≤ (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st).m ∧
      ∀ e ∈ L, f {e} ≤ (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st).m := by
  induction L with
  | nil =>
    intro st
    exact ⟨le_rfl, fun e he => by simp at he⟩
  | cons a L ih =>
    intro st
    simp only [List.foldl_cons]
    obtain ⟨hm1, he1⟩ := step_m f k α ε' a st
    obtain ⟨hm2, he2⟩ := ih (alg2Step p f k α ε' a st).1
    refine ⟨le_trans hm1 hm2, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact le_trans he1 hm2
    · exact he2 e he

lemma guess_finite (ε' c : ℝ) (hq : 1 < 1 + ε') (hc : 0 < c) (k : ℕ) (hk : 1 ≤ k) (m : ℝ) :
    (guessExponents ε' c k m).Finite := by
  have hq0 : (0 : ℝ) < 1 + ε' := by linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hm : m ≤ 0
  · apply Set.finite_empty.subset
    intro h hh
    obtain ⟨_, hb⟩ := hh
    have h1 := (le_div_iff₀ hc).mp hb
    have h2 : 0 < (1 + ε') ^ h * c := mul_pos (zpow_pos hq0 h) hc
    have h3 : m * (k : ℝ) ≤ 0 := by
      nlinarith [mul_nonneg (neg_nonneg.mpr hm) (by linarith : (0:ℝ) ≤ k)]
    exact absurd (lt_of_lt_of_le h2 (le_trans h1 h3)) (lt_irrefl 0)
  · push_neg at hm
    have hA : 0 < m / (1 + ε') := div_pos hm hq0
    have hB : 0 < m * (k : ℝ) / c := div_pos (mul_pos hm (by linarith)) hc
    obtain ⟨a, ha1, _⟩ := exists_mem_Ico_zpow hA hq
    obtain ⟨b, _, hb2⟩ := exists_mem_Ico_zpow hB hq
    apply (Set.finite_Icc a b).subset
    intro h hh
    obtain ⟨hl, hu⟩ := hh
    rw [Set.mem_Icc]
    constructor
    · exact (zpow_le_zpow_iff_right₀ hq).mp (le_trans ha1 hl)
    · have := (zpow_lt_zpow_iff_right₀ hq).mp (lt_of_le_of_lt hu hb2)
      omega

end Aux_StreamSubmod_lemma_15

open Aux_StreamSubmod_lemma_15 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (ε' : ℝ)
    (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ) (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ) (h : ℤ)
    (hT : h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' σ)) (L : List E) (hL : L <+: σ)
    (hnot : h ∉ alg2Guesses k α ε' (alg2Run p f k α ε' L)) (i : Fin p) :
    alg1Sets p f k α ((1 + ε') ^ h) L i = ∅ := by
  have hq : (1 : ℝ) < 1 + ε' := by linarith
  have hq0 : (0 : ℝ) < 1 + ε' := by linarith
  have hc0 : 0 < α / (1 + α) := div_pos hα0 (by linarith)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hmem : ∀ st : Alg2State E p, h ∈ alg2Guesses k α ε' st ↔
      h ∈ guessExponents ε' (α / (1 + α)) k st.m := by
    intro st
    rw [alg2Guesses, guessSet, dif_pos (guess_finite ε' _ hq hc0 k hk st.m),
      Set.Finite.mem_toFinset]
  rw [hmem] at hT hnot
  obtain ⟨t, ht⟩ := hL
  have hrun : alg2Run p f k α ε' σ =
      t.foldl (fun st e => (alg2Step p f k α ε' e st).1) (alg2Run p f k α ε' L) := by
    rw [← ht]
    unfold alg2Run
    rw [List.foldl_append]
  have hmono : (alg2Run p f k α ε' L).m ≤ (alg2Run p f k α ε' σ).m := by
    rw [hrun]
    exact (run_m f k α ε' t _).1
  have hLe : ∀ e ∈ L, f {e} ≤ (alg2Run p f k α ε' L).m :=
    (run_m f k α ε' L (alg2Init p f)).2
  obtain ⟨hT1, _⟩ := hT
  have hbig : (alg2Run p f k α ε' L).m * (k : ℝ) / (α / (1 + α)) < (1 + ε') ^ h := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    show _ ∧ _
    refine ⟨?_, hcon⟩
    have : (alg2Run p f k α ε' L).m / (1 + ε') ≤ (alg2Run p f k α ε' σ).m / (1 + ε') :=
      div_le_div_of_nonneg_right hmono hq0.le
    linarith
  have hθ : (alg2Run p f k α ε' L).m < threshold α k ((1 + ε') ^ h) := by
    unfold threshold
    rw [lt_div_iff₀ hkpos]
    rw [div_lt_iff₀ hc0] at hbig
    linarith
  have hall : ∀ e ∈ L, marginal f e ∅ < threshold α k ((1 + ε') ^ h) := by
    intro e he
    unfold marginal
    have h1 := hLe e he
    have h2 := hf0 ∅
    rw [Finset.insert_empty]
    linarith
  have hsets : alg1Sets p f k α ((1 + ε') ^ h) L = fun _ => ∅ :=
    alg1_empty f k _ L hall
  rw [hsets]
