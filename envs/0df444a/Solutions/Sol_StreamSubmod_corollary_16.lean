-- Prove2me | solution 1 for StreamSubmod.corollary_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:46:12.890261+00:00
-- url     : https://prove2.me/submissions/2c0ce521-d880-4450-890a-1264c65ac344

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1
import Definitions.Def_StreamSubmod_Algorithm2

namespace Aux_StreamSubmod_corollary_16

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

lemma bestOf_mem_ge (f : Finset E → ℝ) (l : List (Finset E)) (x : Finset E) (hx : x ∈ l) :
    f x ≤ f (bestOf f l) := by
  cases l with
  | nil => simp at hx
  | cons A L =>
    show f x ≤ f (L.foldl (better f) A)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (foldl_better f L x).1
    · exact (foldl_better f L A).2 x hx

lemma run_snoc {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (L : List E) (e : E) :
    alg2Run p f k α ε' (L ++ [e]) = (alg2Step p f k α ε' e (alg2Run p f k α ε' L)).1 := by
  unfold alg2Run
  rw [List.foldl_append]
  rfl

lemma alg1_snoc {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (α τ : ℝ) (L : List E) (e : E) :
    alg1Sets p f k α τ (L ++ [e]) = (threshStep f k (threshold α k τ) e (alg1Sets p f k α τ L)).1 := by
  unfold alg1Sets
  rw [List.foldl_append]
  rfl

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

lemma sets_inv {p : ℕ} (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S) (k : ℕ) (hk : 1 ≤ k) (α : ℝ)
    (hα0 : 0 < α) (ε' : ℝ) (hε0 : 0 < ε') (L : List E) :
    ∀ h, h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' L) →
      (alg2Run p f k α ε' L).sets h = alg1Sets p f k α ((1 + ε') ^ h) L := by
  have hq0 : (0 : ℝ) < 1 + ε' := by linarith
  have hc0 : 0 < α / (1 + α) := div_pos hα0 (by linarith)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  induction L using List.reverseRecOn with
  | nil => intro h _; rfl
  | append_singleton L e ih =>
    intro h hh
    rw [run_snoc] at hh ⊢
    rw [alg1_snoc, step_sets, if_pos hh]
    have hkept : (if h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' L) then
        (alg2Run p f k α ε' L).sets h else fun _ => ∅) = alg1Sets p f k α ((1 + ε') ^ h) L := by
      by_cases hold : h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' L)
      · rw [if_pos hold, ih h hold]
      · rw [if_neg hold]
        rw [mem_guess k hk α ε' hα0 hε0] at hold hh
        have hmono := (step_m f k α ε' e (alg2Run p f k α ε' L)).1
        obtain ⟨hh1, _⟩ := hh
        have hlow : (alg2Run p f k α ε' L).m / (1 + ε') ≤ (1 + ε') ^ h := by
          have : (alg2Run p f k α ε' L).m / (1 + ε') ≤
              (alg2Step p f k α ε' e (alg2Run p f k α ε' L)).1.m / (1 + ε') :=
            div_le_div_of_nonneg_right hmono hq0.le
          linarith
        have hbig : (alg2Run p f k α ε' L).m * (k : ℝ) / (α / (1 + α)) < (1 + ε') ^ h := by
          by_contra hcon
          push_neg at hcon
          apply hold
          show _ ∧ _
          exact ⟨hlow, hcon⟩
        have hθ : (alg2Run p f k α ε' L).m < threshold α k ((1 + ε') ^ h) := by
          unfold threshold
          rw [lt_div_iff₀ hkpos]
          rw [div_lt_iff₀ hc0] at hbig
          linarith
        have hLe : ∀ e ∈ L, f {e} ≤ (alg2Run p f k α ε' L).m :=
          (run_m f k α ε' L (alg2Init p f)).2
        have hall : ∀ e ∈ L, marginal f e ∅ < threshold α k ((1 + ε') ^ h) := by
          intro e' he'
          unfold marginal
          have h1 := hLe e' he'
          have h2 := hf0 ∅
          rw [Finset.insert_empty]
          linarith
        exact (alg1_empty f k _ L hall).symm
    rw [hkept]

end A

lemma c16_main {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (ε' : ℝ) (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ)
    (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ) (β : ℝ)
    (hβ : ∀ τ : ℝ, (1 - ε') * optVal f k ≤ τ → τ ≤ optVal f k →
      β * optVal f k ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω)) :
    β * optVal f k ≤ ∑ ω, μ ω * f (alg2Out p f k α ε' Off σ ω) := by
  have hopt0 : 0 ≤ optVal f k := le_trans (hf0 ∅) (le_opt f k ∅ (by simp))
  have hRHS0 : 0 ≤ ∑ ω, μ ω * f (alg2Out p f k α ε' Off σ ω) :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (hOff.prob_nonneg ω) (hf0 _))
  rcases hopt0.lt_or_eq with hOpos | hO0
  swap
  · rw [← hO0, mul_zero]
    exact hRHS0
  have hinit : Inv f k (alg2Init p f : Alg2State E p) := by
    refine ⟨fun h i => by simp [alg2Init], ?_⟩
    exact le_opt f k ∅ (by simp)
  obtain ⟨hI, hm0, hme⟩ := run_inv f k hk α ε' σ _ hinit
  obtain ⟨M, hM⟩ : ∃ M, M = (alg2Run p f k α ε' σ).m := ⟨_, rfl⟩
  have hrun : alg2Run p f k α ε' σ =
      σ.foldl (fun st e => (alg2Step p f k α ε' e st).1) (alg2Init p f) := rfl
  have hMopt : M ≤ optVal f k := by rw [hM, hrun]; exact hI.2
  have hM0 : f ∅ ≤ M := by rw [hM, hrun]; exact hm0
  have hMe : ∀ e, f {e} ≤ M := by
    intro e; rw [hM, hrun]; exact hme e (hσ.2 e)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
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
  have hq : (1 : ℝ) < 1 + ε' := by linarith
  have hq0 : (0 : ℝ) < 1 + ε' := by linarith
  have hc0 : 0 < α / (1 + α) := div_pos hα0 (by linarith)
  have hc1 : α / (1 + α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  obtain ⟨h, hh1, hh2⟩ := exists_mem_Ico_zpow hOpos hq
  have hpow : (1 + ε') ^ (h + 1) = (1 + ε') * (1 + ε') ^ h := by
    rw [zpow_add_one₀ hq0.ne']; ring
  rw [hpow] at hh2
  have hp0 : 0 < (1 + ε') ^ h := zpow_pos hq0 h
  have hhT : h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' σ) := by
    refine (mem_guess k hk α ε' hα0 hε0 _ h).mpr ?_
    rw [← hM]
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hq0]
      nlinarith
    · rw [le_div_iff₀ hc0]
      have : (1 + ε') ^ h * (α / (1 + α)) ≤ (1 + ε') ^ h := by
        nlinarith [mul_le_mul_of_nonneg_left hc1 hp0.le]
      nlinarith
  have hlow : (1 - ε') * optVal f k ≤ (1 + ε') ^ h := by
    have h1 : (1 + ε') * ((1 - ε') * optVal f k) ≤ optVal f k := by
      nlinarith [mul_nonneg (sq_nonneg ε') hOpos.le]
    nlinarith
  have hβ' := hβ _ hlow hh1
  have hsets := sets_inv f hf0 k hk α hα0 ε' hε0 σ h hhT
  calc β * optVal f k ≤ ∑ ω, μ ω * f (alg1Out p f k α ((1 + ε') ^ h) Off σ ω) := hβ'
    _ ≤ ∑ ω, μ ω * f (alg2Out p f k α ε' Off σ ω) := by
      apply Finset.sum_le_sum
      intro ω _
      refine mul_le_mul_of_nonneg_left ?_ (hOff.prob_nonneg ω)
      have e1 : alg1Out p f k α ((1 + ε') ^ h) Off σ ω =
          postProcess f Off ω ((alg2Run p f k α ε' σ).sets h) := by
        rw [hsets]
        rfl
      rw [e1]
      show f _ ≤ f (bestOf f (((alg2Guesses k α ε' (alg2Run p f k α ε' σ)).sort (· ≤ ·)).map
        fun h => postProcess f Off ω ((alg2Run p f k α ε' σ).sets h)))
      exact bestOf_mem_ge f _ _ (List.mem_map.mpr ⟨h, (Finset.mem_sort _).mpr hhT, rfl⟩)

end Aux_StreamSubmod_corollary_16

open Aux_StreamSubmod_corollary_16 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (ε' : ℝ) (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ)
    (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ) (β : ℝ)
    (hβ : ∀ τ : ℝ, (1 - ε') * optVal f k ≤ τ → τ ≤ optVal f k →
      β * optVal f k ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω)) :
    β * optVal f k ≤ ∑ ω, μ ω * f (alg2Out p f k α ε' Off σ ω) :=
  c16_main f hf0 hf k hk α hα0 hα1 μ Off hOff ε' hε0 hε1 p hp σ hσ β hβ
