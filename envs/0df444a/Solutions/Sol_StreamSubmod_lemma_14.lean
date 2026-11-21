-- Prove2me | solution 1 for StreamSubmod.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:12:09.718348+00:00
-- url     : https://prove2.me/submissions/c2e069f4-c8c5-47ce-996e-7e24b96d0ca9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Algorithm2

namespace Aux_StreamSubmod_lemma_14

open StreamSubmod NonmonotoneSubmod.Shared

variable {E : Type} [DecidableEq E]

lemma scan_some {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (i : Fin p) : ∀ l : List (Fin p), (scan f k θ e S l).1 = some i → (S i).card < k := by
  intro l
  induction l with
  | nil => intro h; simp [scan] at h
  | cons j l ih =>
    intro h
    simp only [scan] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h
      subst h
      exact h1
    · exact ih h
    · exact ih h

lemma thresh_card {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (hS : ∀ j, (S j).card ≤ k) (i : Fin p) : ((threshStep f k θ e S).1 i).card ≤ k := by
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
      have := Finset.card_insert_le e (S i)
      omega
    · rw [Function.update_of_ne hij]
      exact hS i

lemma ite_card {p k : ℕ} (c : Prop) [Decidable c] (F : Fin p → Finset E)
    (hF : ∀ j, (F j).card ≤ k) (i : Fin p) :
    ((if c then F else fun _ => (∅ : Finset E)) i).card ≤ k := by
  split_ifs
  · exact hF i
  · simp

abbrev Inv {p : ℕ} [Fintype E] (f : Finset E → ℝ) (k : ℕ) (st : Alg2State E p) : Prop :=
  (∀ h i, (st.sets h i).card ≤ k) ∧ st.m ≤ optVal f k

lemma le_opt [Fintype E] (f : Finset E → ℝ) (k : ℕ) (S : Finset E) (hS : S.card ≤ k) :
    f S ≤ optVal f k := by
  unfold optVal
  have hmem : S ∈ Finset.univ.filter (fun S : Finset E => S.card ≤ k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
  exact Finset.le_sup' (f := f) hmem

lemma step_inv {p : ℕ} [Fintype E] (f : Finset E → ℝ) (k : ℕ) (hk : 1 ≤ k) (α ε' : ℝ) (e : E)
    (st : Alg2State E p) (hI : Inv f k st) :
    Inv f k (alg2Step p f k α ε' e st).1 ∧ st.m ≤ (alg2Step p f k α ε' e st).1.m ∧
      f {e} ≤ (alg2Step p f k α ε' e st).1.m := by
  obtain ⟨hc, hm⟩ := hI
  obtain ⟨M', hM'⟩ : ∃ M', M' = (alg2Guesses k α ε' st ×ˢ (Finset.univ : Finset (Fin p))).fold
      max (f {e}) (fun x => f (st.sets x.1 x.2)) := ⟨_, rfl⟩
  have hmeq : (alg2Step p f k α ε' e st).1.m = if st.m < M' then M' else st.m := by
    rw [hM']; rfl
  have hM'le : M' ≤ optVal f k := by
    rw [hM', Finset.fold_max_le]
    refine ⟨le_opt f k _ (by rw [Finset.card_singleton]; exact hk), ?_⟩
    intro x _
    exact le_opt f k _ (hc _ _)
  have hM'ge : f {e} ≤ M' := by
    rw [hM', Finset.le_fold_max]
    exact Or.inl le_rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro h i
    dsimp only [alg2Step]
    exact ite_card _ _ (thresh_card f k _ e _ (fun j => ite_card _ _ (hc h) j)) i
  · rw [hmeq]
    split_ifs <;> linarith
  · rw [hmeq]
    split_ifs <;> linarith
  · rw [hmeq]
    split_ifs <;> linarith

lemma run_inv {p : ℕ} [Fintype E] (f : Finset E → ℝ) (k : ℕ) (hk : 1 ≤ k) (α ε' : ℝ)
    (L : List E) : ∀ st : Alg2State E p, Inv f k st →
      Inv f k (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st) ∧
      st.m ≤ (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st).m ∧
      ∀ e ∈ L, f {e} ≤ (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st).m := by
  induction L with
  | nil =>
    intro st hI
    exact ⟨hI, le_rfl, fun e he => by simp at he⟩
  | cons a L ih =>
    intro st hI
    simp only [List.foldl_cons]
    obtain ⟨hI1, hm1, he1⟩ := step_inv f k hk α ε' a st hI
    obtain ⟨hI2, hm2, he2⟩ := ih _ hI1
    refine ⟨hI2, le_trans hm1 hm2, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact le_trans he1 hm2
    · exact he2 e he

lemma sub_bound [Fintype E] (f : Finset E → ℝ) (hf : Submodular f) :
    ∀ S : Finset E, f S ≤ f ∅ + ∑ e ∈ S, (f {e} - f ∅) := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := hf {a} S
    have h2 : ({a} : Finset E) ∩ S = ∅ := Finset.singleton_inter_of_notMem ha
    rw [h2, ← Finset.insert_eq] at h1
    linarith

end Aux_StreamSubmod_lemma_14

open Aux_StreamSubmod_lemma_14 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (ε' : ℝ)
    (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ) (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ)
    (hT : (alg2Guesses k α ε' (alg2Run p f k α ε' σ)).Nonempty) :
    ∃ h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' σ),
      (1 - ε') * optVal f k ≤ (1 + ε') ^ h ∧ (1 + ε') ^ h ≤ optVal f k := by
  have hinit : Inv f k (alg2Init p f : Alg2State E p) := by
    refine ⟨fun h i => by simp [alg2Init], ?_⟩
    exact le_opt f k ∅ (by simp)
  obtain ⟨_, hm0, hme⟩ := run_inv f k hk α ε' σ _ hinit
  have hI := (run_inv f k hk α ε' σ _ hinit).1
  obtain ⟨M, hM⟩ : ∃ M, M = (alg2Run p f k α ε' σ).m := ⟨_, rfl⟩
  have hrun : alg2Run p f k α ε' σ =
      σ.foldl (fun st e => (alg2Step p f k α ε' e st).1) (alg2Init p f) := rfl
  have hMopt : M ≤ optVal f k := by rw [hM, hrun]; exact hI.2
  have hM0 : f ∅ ≤ M := by rw [hM, hrun]; exact hm0
  have hMe : ∀ e, f {e} ≤ M := by
    intro e; rw [hM, hrun]; exact hme e (hσ.2 e)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- O ≤ k M
  have hOk : optVal f k ≤ k * M := by
    unfold optVal
    apply Finset.sup'_le
    intro S hS
    have hS' : S.card ≤ k := (Finset.mem_filter.mp hS).2
    have h1 := sub_bound f hf S
    have h2 : ∑ e ∈ S, (f {e} - f ∅) ≤ ∑ e ∈ S, (M - f ∅) :=
      Finset.sum_le_sum fun e _ => by linarith [hMe e]
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have hcS : (S.card : ℝ) ≤ k := by exact_mod_cast hS'
    have hf0' := hf0 ∅
    have hMf : 0 ≤ M - f ∅ := by linarith
    have h3 : (S.card : ℝ) * (M - f ∅) ≤ k * (M - f ∅) := mul_le_mul_of_nonneg_right hcS hMf
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hf0']
  -- guess set finite
  have hfin : (guessExponents ε' (α / (1 + α)) k M).Finite := by
    by_contra hnf
    rw [hM] at hnf
    rw [alg2Guesses, guessSet, dif_neg hnf] at hT
    exact Finset.not_nonempty_empty hT
  have hmem : ∀ h, h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' σ) ↔
      h ∈ guessExponents ε' (α / (1 + α)) k M := by
    intro h
    have hfin' := hfin
    rw [hM] at hfin'
    rw [alg2Guesses, guessSet, dif_pos hfin', Set.Finite.mem_toFinset, hM]
  have hq : (1 : ℝ) < 1 + ε' := by linarith
  have hq0 : (0 : ℝ) < 1 + ε' := by linarith
  have hc0 : 0 < α / (1 + α) := div_pos hα0 (by linarith)
  have hc1 : α / (1 + α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hMpos : 0 < M := by
    obtain ⟨h0, hh0⟩ := hT
    rw [hmem] at hh0
    obtain ⟨_, hb⟩ := hh0
    have hp0 : 0 < (1 + ε') ^ h0 := zpow_pos hq0 h0
    by_contra hM'
    push_neg at hM'
    have : M * (k : ℝ) ≤ 0 := by nlinarith [mul_nonneg (neg_nonneg.mpr hM') (by linarith : (0:ℝ) ≤ k)]
    have : M * (k : ℝ) / (α / (1 + α)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hc0.le
    linarith
  have hOpos : 0 < optVal f k := lt_of_lt_of_le hMpos hMopt
  obtain ⟨h, hh1, hh2⟩ := exists_mem_Ico_zpow hOpos hq
  have hpow : (1 + ε') ^ (h + 1) = (1 + ε') * (1 + ε') ^ h := by
    rw [zpow_add_one₀ hq0.ne']; ring
  rw [hpow] at hh2
  have hp0 : 0 < (1 + ε') ^ h := zpow_pos hq0 h
  refine ⟨h, (hmem h).mpr ⟨?_, ?_⟩, ?_, hh1⟩
  · rw [div_le_iff₀ hq0]
    nlinarith
  · rw [le_div_iff₀ hc0]
    have : (1 + ε') ^ h * (α / (1 + α)) ≤ (1 + ε') ^ h := by
      nlinarith [mul_le_mul_of_nonneg_left hc1 hp0.le]
    nlinarith
  · have h1 : (1 + ε') * ((1 - ε') * optVal f k) ≤ optVal f k := by
      nlinarith [mul_nonneg (sq_nonneg ε') hOpos.le]
    nlinarith
