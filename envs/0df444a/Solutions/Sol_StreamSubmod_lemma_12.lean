-- Prove2me | solution 1 for StreamSubmod.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:01:22.165158+00:00
-- url     : https://prove2.me/submissions/3dc7b8f9-26e5-40c2-a822-e5a80fa738b3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Algorithm2

namespace Aux_StreamSubmod_lemma_12

open StreamSubmod NonmonotoneSubmod.Shared

section A

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

lemma thresh_cases {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) :
    (threshStep f k θ e S).1 = S ∨
      ∃ j, (threshStep f k θ e S).1 = Function.update S j (insert e (S j)) := by
  unfold threshStep
  rcases hs : scan f k θ e S (List.finRange p) with ⟨o, n⟩
  cases o with
  | none => left; rfl
  | some j => right; exact ⟨j, rfl⟩

lemma scan_count {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) :
    ∀ l : List (Fin p), (scan f k θ e S l).2 ≤ l.length := by
  intro l
  induction l with
  | nil => simp [scan]
  | cons i l ih =>
    simp only [scan]
    by_cases h1 : (S i).card < k
    · rw [if_pos h1]
      by_cases h2 : θ ≤ marginal f e (S i)
      · rw [if_pos h2]
        show 1 ≤ l.length + 1
        omega
      · rw [if_neg h2]
        show (scan f k θ e S l).2 + 1 ≤ l.length + 1
        omega
    · rw [if_neg h1]
      show (scan f k θ e S l).2 ≤ l.length + 1
      omega

lemma thresh_count {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) :
    (threshStep f k θ e S).2 = (scan f k θ e S (List.finRange p)).2 := by
  unfold threshStep
  rcases scan f k θ e S (List.finRange p) with ⟨o, n⟩
  cases o <;> rfl

lemma scan_some_c {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
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
    have hj := scan_some_c f k θ e S j (List.finRange p) (by simp [hs])
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

lemma step_sets {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (e : E) (st : Alg2State E p)
    (h : ℤ) :
    (alg2Step p f k α ε' e st).1.sets h =
      if h ∈ alg2Guesses k α ε' (alg2Step p f k α ε' e st).1 then
        (threshStep f k (threshold α k ((1 + ε') ^ h)) e
          (if h ∈ alg2Guesses k α ε' st then st.sets h else fun _ => ∅)).1
      else fun _ => ∅ := rfl

lemma mem_guess {p : ℕ} (k : ℕ) (hk : 1 ≤ k) (α ε' : ℝ) (hα0 : 0 < α) (hε0 : 0 < ε')
    (st : Alg2State E p) (h : ℤ) :
    h ∈ alg2Guesses k α ε' st ↔ h ∈ guessExponents ε' (α / (1 + α)) k st.m := by
  have hq : (1 : ℝ) < 1 + ε' := by linarith
  have hc0 : 0 < α / (1 + α) := div_pos hα0 (by linarith)
  rw [alg2Guesses, guessSet, dif_pos (guess_finite ε' _ hq hc0 k hk st.m),
    Set.Finite.mem_toFinset]


lemma insert_le [Fintype E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (e : E)
    (S : Finset E) : f (insert e S) ≤ f S + f {e} := by
  have h := hf {e} S
  rw [← Finset.insert_eq] at h
  have := hf0 ({e} ∩ S)
  linarith

lemma thresh_val [Fintype E] {p : ℕ} (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) (i : Fin p) :
    f ((threshStep f k θ e S).1 i) ≤ f (S i) + f {e} := by
  have he := hf0 {e}
  rcases thresh_cases f k θ e S with h | ⟨j, h⟩
  · rw [h]
    linarith
  · rw [h]
    by_cases hij : i = j
    · rw [hij, Function.update_self]
      exact insert_le f hf0 hf e (S j)
    · rw [Function.update_of_ne hij]
      linarith

abbrev JInv {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (st : Alg2State E p) : Prop :=
  ∀ h i, f ∅ + ((st.sets h i).card : ℝ) * threshold α k ((1 + ε') ^ h) ≤ f (st.sets h i)

abbrev PInv {p : ℕ} (k : ℕ) (α ε' : ℝ) (st : Alg2State E p) : Prop :=
  ∀ h ∈ alg2Guesses k α ε' st, ∀ i,
    ((st.sets h i).card : ℝ) * (α / (1 + α) * (1 + ε') ^ h) ≤ 2 * st.m * k

lemma step_J {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (e : E) (st : Alg2State E p)
    (hJ : JInv f k α ε' st) : JInv f k α ε' (alg2Step p f k α ε' e st).1 := by
  intro h i
  rw [step_sets]
  by_cases h1 : h ∈ alg2Guesses k α ε' (alg2Step p f k α ε' e st).1
  · rw [if_pos h1]
    apply thresh_inv
    intro j
    by_cases h2 : h ∈ alg2Guesses k α ε' st
    · rw [if_pos h2]
      exact hJ h j
    · rw [if_neg h2]
      simp
  · rw [if_neg h1]
    simp

lemma step_P [Fintype E] {p : ℕ} (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (k : ℕ) (hk : 1 ≤ k) (α ε' : ℝ) (hα0 : 0 < α) (e : E) (st : Alg2State E p)
    (hJ : JInv f k α ε' st) (hm0 : f ∅ ≤ st.m) : PInv k α ε' (alg2Step p f k α ε' e st).1 := by
  intro h hh i
  have hJ' := step_J f k α ε' e st hJ h i
  obtain ⟨M', hM'⟩ : ∃ M', M' = (alg2Guesses k α ε' st ×ˢ (Finset.univ : Finset (Fin p))).fold
      max (f {e}) (fun x => f (st.sets x.1 x.2)) := ⟨_, rfl⟩
  have hmeq : (alg2Step p f k α ε' e st).1.m = if st.m < M' then M' else st.m := by
    rw [hM']; rfl
  have hM'm : M' ≤ (alg2Step p f k α ε' e st).1.m := by
    rw [hmeq]
    split_ifs with hc
    · exact le_rfl
    · exact not_lt.mp hc
  have hstm := step_m f k α ε' e st
  rw [step_sets, if_pos hh] at hJ' ⊢
  obtain ⟨K, hK⟩ : ∃ K : Fin p → Finset E,
      K = if h ∈ alg2Guesses k α ε' st then st.sets h else fun _ => ∅ := ⟨_, rfl⟩
  rw [← hK] at hJ' ⊢
  have hKi : f (K i) ≤ (alg2Step p f k α ε' e st).1.m := by
    by_cases h2 : h ∈ alg2Guesses k α ε' st
    · rw [hK, if_pos h2]
      have : f (st.sets h i) ≤ M' := by
        rw [hM', Finset.le_fold_max]
        right
        exact ⟨(h, i), Finset.mem_product.mpr ⟨h2, Finset.mem_univ i⟩, le_rfl⟩
      linarith
    · rw [hK, if_neg h2]
      linarith [hstm.1]
  have hval := thresh_val f hf0 hf k (threshold α k ((1 + ε') ^ h)) e K i
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hθ : threshold α k ((1 + ε') ^ h) * k = α / (1 + α) * (1 + ε') ^ h := by
    unfold threshold
    exact div_mul_cancel₀ _ hkpos.ne'
  have h0 := hf0 ∅
  have h1 : (((threshStep f k (threshold α k ((1 + ε') ^ h)) e K).1 i).card : ℝ) *
      threshold α k ((1 + ε') ^ h) ≤ 2 * (alg2Step p f k α ε' e st).1.m := by
    linarith [hstm.2]
  have h2 := mul_le_mul_of_nonneg_right h1 hkpos.le
  calc (((threshStep f k (threshold α k ((1 + ε') ^ h)) e K).1 i).card : ℝ) *
        (α / (1 + α) * (1 + ε') ^ h)
      = (((threshStep f k (threshold α k ((1 + ε') ^ h)) e K).1 i).card : ℝ) *
        threshold α k ((1 + ε') ^ h) * k := by rw [mul_assoc, hθ]
    _ ≤ 2 * (alg2Step p f k α ε' e st).1.m * k := h2

lemma run_JP [Fintype E] {p : ℕ} (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (k : ℕ) (hk : 1 ≤ k) (α ε' : ℝ) (hα0 : 0 < α) (L : List E) :
    ∀ st : Alg2State E p, JInv f k α ε' st → f ∅ ≤ st.m → PInv k α ε' st →
      JInv f k α ε' (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st) ∧
      f ∅ ≤ (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st).m ∧
      PInv k α ε' (L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st) := by
  induction L with
  | nil => intro st hJ hm hP; exact ⟨hJ, hm, hP⟩
  | cons a L ih =>
    intro st hJ hm hP
    simp only [List.foldl_cons]
    apply ih
    · exact step_J f k α ε' a st hJ
    · exact le_trans hm (step_m f k α ε' a st).1
    · exact step_P f hf0 hf k hk α ε' hα0 a st hJ hm

lemma count_le (q A B : ℝ) (hq : 1 < q) (hA : 0 < A) (T : Finset ℤ) (hT : T.Nonempty)
    (hmem : ∀ h ∈ T, A ≤ q ^ h ∧ q ^ h ≤ B) :
    (T.card : ℝ) ≤ Real.log (B / A) / Real.log q + 1 := by
  have hq0 : 0 < q := by linarith
  have hlq : 0 < Real.log q := Real.log_pos hq
  obtain ⟨h0, hh0⟩ : ∃ h0, h0 = T.min' hT := ⟨_, rfl⟩
  have hh0T : h0 ∈ T := by rw [hh0]; exact Finset.min'_mem T hT
  obtain ⟨X, hX⟩ : ∃ X, X = Real.log (B / A) / Real.log q := ⟨_, rfl⟩
  have hdiff : ∀ h ∈ T, ((h - h0 : ℤ) : ℝ) ≤ X := by
    intro h hh
    obtain ⟨_, hB⟩ := hmem h hh
    obtain ⟨hA0, _⟩ := hmem h0 hh0T
    have hpow : q ^ h = q ^ h0 * q ^ (h - h0) := by
      rw [← zpow_add₀ hq0.ne']
      congr 1
      ring
    have hp : 0 < q ^ (h - h0) := zpow_pos hq0 _
    have h1 : q ^ (h - h0) ≤ B / A := by
      rw [le_div_iff₀ hA]
      calc q ^ (h - h0) * A ≤ q ^ (h - h0) * q ^ h0 := mul_le_mul_of_nonneg_left hA0 hp.le
        _ = q ^ h := by rw [hpow]; ring
        _ ≤ B := hB
    have h2 : Real.log (q ^ (h - h0)) ≤ Real.log (B / A) := Real.log_le_log hp h1
    rw [Real.log_zpow] at h2
    rw [hX, le_div_iff₀ hlq]
    exact h2
  have hX0 : 0 ≤ X := by
    have := hdiff h0 hh0T
    rw [sub_self, Int.cast_zero] at this
    exact this
  have hsub : T ⊆ Finset.Icc h0 (h0 + ⌊X⌋) := by
    intro h hh
    rw [Finset.mem_Icc]
    constructor
    · rw [hh0]
      exact Finset.min'_le T h hh
    · have h1 := hdiff h hh
      have h2 : h - h0 ≤ ⌊X⌋ := Int.le_floor.mpr h1
      omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hfl : (0 : ℤ) ≤ ⌊X⌋ := Int.floor_nonneg.mpr hX0
  have he : h0 + ⌊X⌋ + 1 - h0 = ⌊X⌋ + 1 := by ring
  rw [he] at hcard
  have hc1 : ((T.card : ℕ) : ℤ) ≤ (((⌊X⌋ + 1).toNat : ℕ) : ℤ) := by exact_mod_cast hcard
  rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ ⌊X⌋ + 1 by omega)] at hc1
  have hc3 : ((T.card : ℤ) : ℝ) ≤ ((⌊X⌋ + 1 : ℤ) : ℝ) := by exact_mod_cast hc1
  push_cast at hc3
  have := Int.floor_le X
  rw [← hX]
  linarith

lemma geom_finset (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (J : Finset ℕ) :
    ∑ j ∈ J, x ^ j ≤ 1 / (1 - x) := by
  have hJ : J ⊆ Finset.range (J.sup id + 1) := fun j hj =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  calc ∑ j ∈ J, x ^ j ≤ ∑ j ∈ Finset.range (J.sup id + 1), x ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hJ (fun _ _ _ => pow_nonneg hx0 _)
    _ ≤ 1 / (1 - x) := by
        have hg := geom_sum_mul x (J.sup id + 1)
        rw [le_div_iff₀ (by linarith)]
        have := pow_nonneg hx0 (J.sup id + 1)
        linarith

lemma geom_part (q R : ℝ) (hq : 1 < q) (hR : 0 < R) (H : Finset ℤ)
    (hH : ∀ h ∈ H, R < q ^ h) : ∑ h ∈ H, R / q ^ h ≤ 1 / (1 - q⁻¹) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨h1, hh1, hh2⟩ := exists_mem_Ico_zpow hR hq
  have hge : ∀ h ∈ H, h1 + 1 ≤ h := by
    intro h hh
    by_contra hlt
    push_neg at hlt
    have : q ^ h ≤ q ^ h1 := zpow_le_zpow_right₀ hq.le (by omega)
    linarith [hH h hh]
  have hbound : ∀ h ∈ H, R / q ^ h ≤ q⁻¹ ^ (h - h1 - 1).toNat := by
    intro h hh
    have hd : ((h - h1 - 1).toNat : ℤ) = h - h1 - 1 := Int.toNat_of_nonneg (by have := hge h hh; omega)
    have hqh : 0 < q ^ h := zpow_pos hq0 h
    have e1 : q⁻¹ ^ (h - h1 - 1).toNat = q ^ (h1 + 1) / q ^ h := by
      rw [inv_pow, ← zpow_natCast, hd, ← zpow_neg, ← zpow_sub₀ hq0.ne']
      congr 1
      ring
    rw [e1]
    exact div_le_div_of_nonneg_right hh2.le hqh.le
  have hinj : Set.InjOn (fun h : ℤ => (h - h1 - 1).toNat) (H : Set ℤ) := by
    intro a ha b hb hab
    have ha' := hge a ha
    have hb' := hge b hb
    simp only at hab
    have hc := congrArg (fun n : ℕ => (n : ℤ)) hab
    simp only [Int.toNat_of_nonneg (show (0 : ℤ) ≤ a - h1 - 1 by omega),
      Int.toNat_of_nonneg (show (0 : ℤ) ≤ b - h1 - 1 by omega)] at hc
    omega
  calc ∑ h ∈ H, R / q ^ h ≤ ∑ h ∈ H, q⁻¹ ^ (h - h1 - 1).toNat := Finset.sum_le_sum hbound
    _ = ∑ j ∈ H.image (fun h : ℤ => (h - h1 - 1).toNat), q⁻¹ ^ j := (Finset.sum_image hinj).symm
    _ ≤ 1 / (1 - q⁻¹) := geom_finset q⁻¹ (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq) _

lemma step_count {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (e : E) (st : Alg2State E p) :
    (alg2Step p f k α ε' e st).2 = 1 + (alg2Guesses k α ε' st ×ˢ (Finset.univ : Finset (Fin p))).card +
      ∑ h ∈ alg2Guesses k α ε' (alg2Step p f k α ε' e st).1,
        (threshStep f k (threshold α k ((1 + ε') ^ h)) e
          (if h ∈ alg2Guesses k α ε' st then st.sets h else fun _ => ∅)).2 := rfl

lemma mem_guess' {p : ℕ} (k : ℕ) (hk : 1 ≤ k) (α ε' : ℝ) (hα0 : 0 < α) (hε0 : 0 < ε')
    (st : Alg2State E p) (h : ℤ) :
    h ∈ alg2Guesses k α ε' st ↔
      (st.m / (1 + ε') ≤ (1 + ε') ^ h ∧ (1 + ε') ^ h ≤ st.m * k / (α / (1 + α))) :=
  mem_guess k hk α ε' hα0 hε0 st h

lemma guess_card {p : ℕ} (k : ℕ) (hk : 1 ≤ k) (α ε' : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hε0 : 0 < ε') (hε1 : ε' < 1) (st : Alg2State E p) :
    ((alg2Guesses k α ε' st).card : ℝ) ≤ 7 * ε'⁻¹ * (1 + Real.log ((k : ℝ) / α)) := by
  have hq : (1 : ℝ) < 1 + ε' := by linarith
  have hq0 : (0 : ℝ) < 1 + ε' := by linarith
  have hc0 : 0 < α / (1 + α) := div_pos hα0 (by linarith)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkα : 1 ≤ (k : ℝ) / α := by rw [le_div_iff₀ hα0]; linarith
  have hlk : 0 ≤ Real.log ((k : ℝ) / α) := Real.log_nonneg hkα
  have hs1 : 1 ≤ ε'⁻¹ := one_le_inv₀ hε0 |>.mpr hε1.le
  have hlq : ε' / 2 ≤ Real.log (1 + ε') := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hq0)
    rw [Real.log_inv] at h
    have hi : (1 + ε')⁻¹ ≤ 1 - ε' / 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hq0]
      nlinarith
    linarith
  have hB : (1 + ε') * k / (α / (1 + α)) ≤ 4 * ((k : ℝ) / α) := by
    rw [div_div_eq_mul_div]
    rw [show 4 * ((k : ℝ) / α) = 4 * k / α by ring]
    refine div_le_div_of_nonneg_right ?_ hα0.le
    have h4 : (1 + ε') * (1 + α) ≤ 4 := by nlinarith
    have h5 := mul_le_mul_of_nonneg_right h4 (by linarith : (0 : ℝ) ≤ k)
    linarith
  have hB1 : 1 ≤ (1 + ε') * k / (α / (1 + α)) := by
    rw [le_div_iff₀ hc0]
    have : α / (1 + α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have hlogB : Real.log ((1 + ε') * k / (α / (1 + α))) ≤ 3 + Real.log ((k : ℝ) / α) := by
    have h1 := Real.log_le_log (by linarith) hB
    rw [Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num)
      (show (k : ℝ) / α ≠ 0 from (div_pos (by linarith) hα0).ne')] at h1
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hlogB0 : 0 ≤ Real.log ((1 + ε') * k / (α / (1 + α))) := Real.log_nonneg hB1
  have hdiv : Real.log ((1 + ε') * k / (α / (1 + α))) / Real.log (1 + ε') ≤
      2 * (3 + Real.log ((k : ℝ) / α)) * ε'⁻¹ := by
    calc Real.log ((1 + ε') * k / (α / (1 + α))) / Real.log (1 + ε')
        ≤ Real.log ((1 + ε') * k / (α / (1 + α))) / (ε' / 2) :=
          div_le_div_of_nonneg_left hlogB0 (by linarith) hlq
      _ ≤ (3 + Real.log ((k : ℝ) / α)) / (ε' / 2) :=
          div_le_div_of_nonneg_right hlogB (by linarith)
      _ = 2 * (3 + Real.log ((k : ℝ) / α)) * ε'⁻¹ := by rw [div_div_eq_mul_div]; ring
  have hmain : ((alg2Guesses k α ε' st).card : ℝ) ≤
      Real.log ((1 + ε') * k / (α / (1 + α))) / Real.log (1 + ε') + 1 := by
    by_cases hne : (alg2Guesses k α ε' st).Nonempty
    · obtain ⟨h0, hh0⟩ := hne
      have hmpos : 0 < st.m := by
        rw [mem_guess' k hk α ε' hα0 hε0] at hh0
        obtain ⟨_, hb⟩ := hh0
        have hp0 : 0 < (1 + ε') ^ h0 := zpow_pos hq0 h0
        by_contra hm
        push_neg at hm
        have : st.m * (k : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm (by linarith)
        have : st.m * (k : ℝ) / (α / (1 + α)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hc0.le
        linarith
      have hc := count_le (1 + ε') (st.m / (1 + ε')) (st.m * k / (α / (1 + α))) hq
        (div_pos hmpos hq0) _ ⟨h0, hh0⟩ (fun h hh => (mem_guess' k hk α ε' hα0 hε0 st h).mp hh)
      have hm' : st.m ≠ 0 := hmpos.ne'
      have hq' : (1 + ε') ≠ 0 := hq0.ne'
      have hα' : α ≠ 0 := hα0.ne'
      have h1α : (1 + α) ≠ 0 := by linarith
      have he : st.m * k / (α / (1 + α)) / (st.m / (1 + ε')) = (1 + ε') * k / (α / (1 + α)) := by
        first | (field_simp; done) | (field_simp; ring)
      rw [he] at hc
      exact hc
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      have := div_nonneg hlogB0 (Real.log_nonneg hq.le)
      linarith
  have hlkε : 0 ≤ Real.log ((k : ℝ) / α) * ε'⁻¹ := mul_nonneg hlk (by linarith)
  linarith

lemma stored_bound [Fintype E] {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (hk : 1 ≤ k) (α ε' : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hε0 : 0 < ε') (hε1 : ε' < 1) (st : Alg2State E p)
    (hcard : ∀ h i, (st.sets h i).card ≤ k) (hP : PInv k α ε' st) :
    (alg2Stored k α ε' st : ℝ) ≤ 20 * (p : ℝ) * (k : ℝ) * ε'⁻¹ * (1 + Real.log α⁻¹) := by
  have hq : (1 : ℝ) < 1 + ε' := by linarith
  have hq0 : (0 : ℝ) < 1 + ε' := by linarith
  have hc0 : 0 < α / (1 + α) := div_pos hα0 (by linarith)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs1 : 1 ≤ ε'⁻¹ := one_le_inv₀ hε0 |>.mpr hε1.le
  have hla : 0 ≤ Real.log α⁻¹ := by
    rw [Real.log_inv]
    have := Real.log_nonpos hα0.le hα1
    linarith
  have hlq : ε' / 2 ≤ Real.log (1 + ε') := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hq0)
    rw [Real.log_inv] at h
    have hi : (1 + ε')⁻¹ ≤ 1 - ε' / 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hq0]
      nlinarith
    linarith
  have hgeo : 1 / (1 - (1 + ε')⁻¹) ≤ 2 * ε'⁻¹ := by
    have hi : (1 + ε')⁻¹ ≤ 1 - ε' / 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hq0]
      nlinarith
    calc 1 / (1 - (1 + ε')⁻¹) ≤ 1 / (ε' / 2) := one_div_le_one_div_of_le (by linarith) (by linarith)
      _ = 2 * ε'⁻¹ := by rw [one_div_div]; ring
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  unfold alg2Stored
  push_cast
  by_cases hne : (alg2Guesses k α ε' st).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    have : 0 ≤ (p : ℝ) * (k : ℝ) * ε'⁻¹ * (1 + Real.log α⁻¹) :=
      mul_nonneg (mul_nonneg (mul_nonneg hp0 (Nat.cast_nonneg k)) (by linarith)) (by linarith)
    linarith
  obtain ⟨h0, hh0⟩ := hne
  have hmpos : 0 < st.m := by
    rw [mem_guess' k hk α ε' hα0 hε0] at hh0
    obtain ⟨_, hb⟩ := hh0
    have hp0' : 0 < (1 + ε') ^ h0 := zpow_pos hq0 h0
    by_contra hm
    push_neg at hm
    have : st.m * (k : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm (by linarith)
    have : st.m * (k : ℝ) / (α / (1 + α)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hc0.le
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 * st.m / (α / (1 + α)) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hR]; exact div_pos (by linarith) hc0
  have hm' : st.m ≠ 0 := hmpos.ne'
  have hq' : (1 + ε') ≠ 0 := hq0.ne'
  have hα' : α ≠ 0 := hα0.ne'
  have h1α : (1 + α) ≠ 0 := by linarith
  have hg1 : ∀ h ∈ alg2Guesses k α ε' st, ∑ i, ((st.sets h i).card : ℝ) ≤ p * k := by
    intro h _
    have : ∑ i : Fin p, ((st.sets h i).card : ℝ) ≤ ∑ _i : Fin p, (k : ℝ) :=
      Finset.sum_le_sum (fun i _ => by exact_mod_cast hcard h i)
    simpa using this
  have hg2 : ∀ h ∈ alg2Guesses k α ε' st, ∑ i, ((st.sets h i).card : ℝ) ≤
      p * (k * (R / (1 + ε') ^ h)) := by
    intro h hh
    have hqh : 0 < (1 + ε') ^ h := zpow_pos hq0 h
    have hcq : 0 < α / (1 + α) * (1 + ε') ^ h := mul_pos hc0 hqh
    have hb : ∀ i, ((st.sets h i).card : ℝ) ≤ k * (R / (1 + ε') ^ h) := by
      intro i
      have h1 := hP h hh i
      have h2 : ((st.sets h i).card : ℝ) ≤ 2 * st.m * k / (α / (1 + α) * (1 + ε') ^ h) :=
        (le_div_iff₀ hcq).mpr h1
      have h3 : 2 * st.m * k / (α / (1 + α) * (1 + ε') ^ h) = k * (R / (1 + ε') ^ h) := by
        rw [hR]
        ring
      linarith
    have : ∑ i : Fin p, ((st.sets h i).card : ℝ) ≤ ∑ _i : Fin p, (k * (R / (1 + ε') ^ h)) :=
      Finset.sum_le_sum (fun i _ => hb i)
    simpa using this
  rw [← Finset.sum_filter_add_sum_filter_not (alg2Guesses k α ε' st)
    (fun h => (1 + ε') ^ h ≤ R)]
  have hpart1 : ∑ h ∈ (alg2Guesses k α ε' st).filter (fun h => (1 + ε') ^ h ≤ R),
      ∑ i, ((st.sets h i).card : ℝ) ≤
        ((alg2Guesses k α ε' st).filter (fun h => (1 + ε') ^ h ≤ R)).card * (p * k) := by
    have := Finset.sum_le_sum (s := (alg2Guesses k α ε' st).filter (fun h => (1 + ε') ^ h ≤ R))
      (fun h hh => hg1 h (Finset.mem_filter.mp hh).1)
    simpa using this
  have hpart2 : ∑ h ∈ (alg2Guesses k α ε' st).filter (fun h => ¬ (1 + ε') ^ h ≤ R),
      ∑ i, ((st.sets h i).card : ℝ) ≤ p * k * (1 / (1 - (1 + ε')⁻¹)) := by
    have h1 := Finset.sum_le_sum
      (s := (alg2Guesses k α ε' st).filter (fun h => ¬ (1 + ε') ^ h ≤ R))
      (fun h hh => hg2 h (Finset.mem_filter.mp hh).1)
    have h2 := geom_part (1 + ε') R hq hRpos
      ((alg2Guesses k α ε' st).filter (fun h => ¬ (1 + ε') ^ h ≤ R))
      (fun h hh => not_le.mp (Finset.mem_filter.mp hh).2)
    have h3 : ∑ h ∈ (alg2Guesses k α ε' st).filter (fun h => ¬ (1 + ε') ^ h ≤ R),
        (p : ℝ) * (k * (R / (1 + ε') ^ h)) =
        p * k * ∑ h ∈ (alg2Guesses k α ε' st).filter (fun h => ¬ (1 + ε') ^ h ≤ R),
          R / (1 + ε') ^ h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    have hpk : (0 : ℝ) ≤ p * k := by positivity
    have h4 := mul_le_mul_of_nonneg_left h2 hpk
    linarith
  have hH1 : (((alg2Guesses k α ε' st).filter (fun h => (1 + ε') ^ h ≤ R)).card : ℝ) ≤
      Real.log (2 * (1 + ε') / (α / (1 + α))) / Real.log (1 + ε') + 1 := by
    have hB1 : 1 ≤ 2 * (1 + ε') / (α / (1 + α)) := by
      rw [le_div_iff₀ hc0]
      have : α / (1 + α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    by_cases hne : ((alg2Guesses k α ε' st).filter (fun h => (1 + ε') ^ h ≤ R)).Nonempty
    · have hc := count_le (1 + ε') (st.m / (1 + ε')) R hq (div_pos hmpos hq0) _ hne
        (fun h hh => ⟨((mem_guess' k hk α ε' hα0 hε0 st h).mp (Finset.mem_filter.mp hh).1).1,
          (Finset.mem_filter.mp hh).2⟩)
      have he : R / (st.m / (1 + ε')) = 2 * (1 + ε') / (α / (1 + α)) := by
        rw [hR]
        first | (field_simp; done) | (field_simp; ring)
      rw [he] at hc
      exact hc
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      have := div_nonneg (Real.log_nonneg hB1) (Real.log_nonneg hq.le)
      linarith
  have hlogB : Real.log (2 * (1 + ε') / (α / (1 + α))) ≤ 7 + Real.log α⁻¹ := by
    have hle : 2 * (1 + ε') / (α / (1 + α)) ≤ 8 * α⁻¹ := by
      rw [div_div_eq_mul_div, show 8 * α⁻¹ = 8 / α by ring]
      refine div_le_div_of_nonneg_right ?_ hα0.le
      nlinarith
    have hpos : 0 < 2 * (1 + ε') / (α / (1 + α)) := div_pos (by linarith) hc0
    have h1 := Real.log_le_log hpos hle
    rw [Real.log_mul (show (8 : ℝ) ≠ 0 by norm_num) (show α⁻¹ ≠ 0 from (inv_pos.mpr hα0).ne')] at h1
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
    linarith
  have hlogB0 : 0 ≤ Real.log (2 * (1 + ε') / (α / (1 + α))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc0]
    have : α / (1 + α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have hdiv : Real.log (2 * (1 + ε') / (α / (1 + α))) / Real.log (1 + ε') ≤
      2 * (7 + Real.log α⁻¹) * ε'⁻¹ := by
    calc Real.log (2 * (1 + ε') / (α / (1 + α))) / Real.log (1 + ε')
        ≤ Real.log (2 * (1 + ε') / (α / (1 + α))) / (ε' / 2) :=
          div_le_div_of_nonneg_left hlogB0 (by linarith) hlq
      _ ≤ (7 + Real.log α⁻¹) / (ε' / 2) := div_le_div_of_nonneg_right hlogB (by linarith)
      _ = 2 * (7 + Real.log α⁻¹) * ε'⁻¹ := by rw [div_div_eq_mul_div]; ring
  have hX : (((alg2Guesses k α ε' st).filter (fun h => (1 + ε') ^ h ≤ R)).card : ℝ) +
      1 / (1 - (1 + ε')⁻¹) ≤ 20 * ε'⁻¹ * (1 + Real.log α⁻¹) := by
    have hls : 0 ≤ Real.log α⁻¹ * ε'⁻¹ := mul_nonneg hla (by linarith)
    linarith
  have hpk : (0 : ℝ) ≤ p * k := by positivity
  have hfin := mul_le_mul_of_nonneg_left hX hpk
  linarith

lemma queries_bound {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (hk : 1 ≤ k) (hp : 1 ≤ p) (α ε' : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hε0 : 0 < ε') (hε1 : ε' < 1) (e : E) (st : Alg2State E p) :
    ((alg2Step p f k α ε' e st).2 : ℝ) ≤ 20 * (p : ℝ) * ε'⁻¹ * (1 + Real.log ((k : ℝ) / α)) := by
  rw [step_count]
  have hT := guess_card k hk α ε' hα0 hα1 hε0 hε1 st
  have hT1 := guess_card k hk α ε' hα0 hα1 hε0 hε1 (alg2Step p f k α ε' e st).1
  have hterm : ∀ h ∈ alg2Guesses k α ε' (alg2Step p f k α ε' e st).1,
      ((threshStep f k (threshold α k ((1 + ε') ^ h)) e
        (if h ∈ alg2Guesses k α ε' st then st.sets h else fun _ => ∅)).2 : ℝ) ≤ p := by
    intro h _
    have := scan_count f k (threshold α k ((1 + ε') ^ h)) e
      (if h ∈ alg2Guesses k α ε' st then st.sets h else fun _ => ∅) (List.finRange p)
    rw [List.length_finRange, ← thresh_count] at this
    exact_mod_cast this
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hs
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  push_cast
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs1 : 1 ≤ ε'⁻¹ := one_le_inv₀ hε0 |>.mpr hε1.le
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkα : 1 ≤ (k : ℝ) / α := by rw [le_div_iff₀ hα0]; linarith
  have hlk : 0 ≤ Real.log ((k : ℝ) / α) := Real.log_nonneg hkα
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have m1 := mul_le_mul_of_nonneg_left hT hp0
  have m2 := mul_le_mul_of_nonneg_left hT1 hp0
  have hps : 1 ≤ (p : ℝ) * ε'⁻¹ := one_le_mul_of_one_le_of_one_le hp1 hs1
  have hone : 1 ≤ (p : ℝ) * ε'⁻¹ * (1 + Real.log ((k : ℝ) / α)) :=
    one_le_mul_of_one_le_of_one_le hps (by linarith)
  linarith

end A

lemma lemma12_main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ ε' : ℝ, 0 < ε' → ε' < 1 →
      ∀ p : ℕ, 1 ≤ p →
      ∀ σ : List E, IsStream σ →
      (∀ L, L <+: σ →
        (alg2Stored k α ε' (alg2Run p f k α ε' L) : ℝ) ≤
          C * (p : ℝ) * (k : ℝ) * ε'⁻¹ * (1 + Real.log α⁻¹)) ∧
      (∀ L e, L ++ [e] <+: σ →
        (alg2Queries p f k α ε' L e : ℝ) ≤
          C * (p : ℝ) * ε'⁻¹ * (1 + Real.log ((k : ℝ) / α))) := by
  refine ⟨20, by norm_num, ?_⟩
  intro E _ _ f hf0 hf k hk α hα0 hα1 ε' hε0 hε1 p hp σ _
  constructor
  · intro L _
    have hinit : Inv f k (alg2Init p f : Alg2State E p) := by
      refine ⟨fun h i => by simp [alg2Init], ?_⟩
      exact le_opt f k ∅ (by simp)
    have hrun : alg2Run p f k α ε' L =
        L.foldl (fun st e => (alg2Step p f k α ε' e st).1) (alg2Init p f) := rfl
    have hI := (run_inv f k hk α ε' L _ hinit).1
    have hJ0 : JInv f k α ε' (alg2Init p f : Alg2State E p) := by
      intro h i
      simp [alg2Init]
    have hP0 : PInv k α ε' (alg2Init p f : Alg2State E p) := by
      intro h _ i
      simp only [alg2Init, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (by norm_num) (hf0 ∅)) (Nat.cast_nonneg k)
    have hJP := run_JP f hf0 hf k hk α ε' hα0 L (alg2Init p f) hJ0 le_rfl hP0
    rw [hrun]
    exact stored_bound f k hk α ε' hα0 hα1 hε0 hε1 _ hI.1 hJP.2.2
  · intro L e _
    exact queries_bound f k hk hp α ε' hα0 hα1 hε0 hε1 e (alg2Run p f k α ε' L)

end Aux_StreamSubmod_lemma_12

open Aux_StreamSubmod_lemma_12 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ ε' : ℝ, 0 < ε' → ε' < 1 →
      ∀ p : ℕ, 1 ≤ p →
      ∀ σ : List E, IsStream σ →
      (∀ L, L <+: σ →
        (alg2Stored k α ε' (alg2Run p f k α ε' L) : ℝ) ≤
          C * (p : ℝ) * (k : ℝ) * ε'⁻¹ * (1 + Real.log α⁻¹)) ∧
      (∀ L e, L ++ [e] <+: σ →
        (alg2Queries p f k α ε' L e : ℝ) ≤
          C * (p : ℝ) * ε'⁻¹ * (1 + Real.log ((k : ℝ) / α))) :=
  lemma12_main
