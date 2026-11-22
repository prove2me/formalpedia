-- Prove2me | solution 1 for StreamSubmod.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T22:09:09.760851+00:00
-- url     : https://prove2.me/submissions/ecf32316-b5be-4998-816f-07c77bb3de11

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1
import Definitions.Def_StreamSubmod_Algorithm2
import Theorems.Thm_StreamSubmod_proposition_8

/-! ===== SS_Common ===== -/

/-! # Shared facts: every maintained set has at most `k` elements, so every output does. -/

namespace SSCommon
open StreamSubmod

variable {E : Type} [DecidableEq E]

theorem scan_lt {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) :
    ∀ (l : List (Fin p)) (i : Fin p), (scan f k θ e S l).1 = some i → (S i).card < k
  | [], i, h => by simp [scan] at h
  | j :: l, i, h => by
    unfold scan at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h
      subst h; exact h1
    · exact scan_lt f k θ e S l i h
    · exact scan_lt f k θ e S l i h

theorem threshStep_card {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E)
    (S : Fin p → Finset E) (hS : ∀ i, (S i).card ≤ k) :
    ∀ i, ((threshStep f k θ e S).1 i).card ≤ k := by
  intro i
  unfold threshStep
  rcases h : scan f k θ e S (List.finRange p) with ⟨_ | j, n⟩
  · exact hS i
  · have hj := scan_lt f k θ e S _ j (by rw [h])
    simp only
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · rw [Function.update_of_ne hij]; exact hS i

theorem alg1Sets_card (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α τ : ℝ) (L : List E) :
    ∀ i, (alg1Sets p f k α τ L i).card ≤ k := by
  unfold alg1Sets
  suffices H : ∀ (L : List E) (S : Fin p → Finset E), (∀ i, (S i).card ≤ k) →
      ∀ i, (L.foldl (fun S e => (threshStep f k (threshold α k τ) e S).1) S i).card ≤ k from
    H L _ (fun _ => by simp)
  intro L
  induction L with
  | nil => intro S hS; simpa using hS
  | cons e L ih =>
    intro S hS
    exact ih _ (threshStep_card f k _ e S hS)

theorem foldl_better_mem (f : Finset E → ℝ) :
    ∀ (L : List (Finset E)) (A : Finset E), L.foldl (better f) A = A ∨ L.foldl (better f) A ∈ L
  | [], A => Or.inl rfl
  | B :: L, A => by
    rw [List.foldl_cons]
    rcases foldl_better_mem f L (better f A B) with h | h
    · rw [h]; unfold better; split_ifs
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem bestOf_card (f : Finset E → ℝ) (k : ℕ) (L : List (Finset E))
    (hL : ∀ A ∈ L, A.card ≤ k) : (bestOf f L).card ≤ k := by
  cases L with
  | nil => simp [bestOf]
  | cons A L =>
    simp only [bestOf]
    rcases foldl_better_mem f L A with h | h
    · rw [h]; exact hL A (List.mem_cons_self ..)
    · exact hL _ (List.mem_cons_of_mem _ h)

theorem postProcess_card {Ω : Type} {p : ℕ} [Fintype E] (f : Finset E → ℝ) (k : ℕ)
    (Off : Ω → Finset E → Finset E) (hOff : ∀ ω U, (Off ω U).card ≤ k) (ω : Ω)
    (S : Fin p → Finset E) (hS : ∀ i, (S i).card ≤ k) : (postProcess f Off ω S).card ≤ k := by
  unfold postProcess
  apply bestOf_card
  intro A hA
  rcases List.mem_cons.1 hA with h | h
  · rw [h]; exact hOff _ _
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact hS i

theorem alg2Step_card (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (e : E)
    (st : Alg2State E p) (hst : ∀ h i, (st.sets h i).card ≤ k) :
    ∀ h i, ((alg2Step p f k α ε' e st).1.sets h i).card ≤ k := by
  intro h i
  simp only [alg2Step]
  split_ifs <;>
    first
    | simp
    | (apply threshStep_card; intro j; split_ifs <;> first | exact hst _ _ | simp)
    | (apply threshStep_card; intro j; first | exact hst _ _ | simp)

theorem alg2Run_card (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (L : List E) :
    ∀ h i, ((alg2Run p f k α ε' L).sets h i).card ≤ k := by
  unfold alg2Run
  suffices H : ∀ (L : List E) (st : Alg2State E p), (∀ h i, (st.sets h i).card ≤ k) →
      ∀ h i, ((L.foldl (fun st e => (alg2Step p f k α ε' e st).1) st).sets h i).card ≤ k from
    H L _ (fun _ _ => by simp [alg2Init])
  intro L
  induction L with
  | nil => intro st hst; simpa using hst
  | cons e L ih =>
    intro st hst
    exact ih _ (alg2Step_card p f k α ε' e st hst)

theorem optVal_nonneg [Fintype E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S) (k : ℕ) :
    0 ≤ optVal f k := by
  unfold optVal
  exact (hf0 ∅).trans (Finset.le_sup' f (by simp))

end SSCommon

/-! ===== SS_Thm9 ===== -/

/-! # Theorem 9 from Proposition 8 with `p = ⌈4/ε⌉`. -/

namespace SSThm9
open StreamSubmod NonmonotoneSubmod.Shared

theorem p_bounds (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ ⌈4 / ε⌉₊ ∧ 2 * ((⌈4 / ε⌉₊ : ℕ) : ℝ)⁻¹ ≤ ε / 2 ∧ ((⌈4 / ε⌉₊ : ℕ) : ℝ) ≤ 5 * ε⁻¹ := by
  have h4 : 4 ≤ 4 / ε := by rw [le_div_iff₀ hε]; linarith
  have hc : 4 / ε ≤ ((⌈4 / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hc2 : ((⌈4 / ε⌉₊ : ℕ) : ℝ) < 4 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hpos : (0 : ℝ) < ((⌈4 / ε⌉₊ : ℕ) : ℝ) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (show (1 : ℝ) ≤ ((⌈4 / ε⌉₊ : ℕ) : ℝ) by linarith)
  · rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have : 4 ≤ ε * ((⌈4 / ε⌉₊ : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hc hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    linarith
  · have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.2 hε1
    have : 4 / ε = 4 * ε⁻¹ := div_eq_mul_inv _ _
    linarith

theorem value_bound (a ε τ O p S : ℝ) (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hO : 0 ≤ O) (hτ1 : (1 - ε / 2) * O ≤ τ) (hp : 2 * p ≤ ε / 2) (hS0 : 0 ≤ S)
    (hS : (a - 2 * p) * τ ≤ S) : (a - ε) * O ≤ S := by
  by_cases hae : a - ε ≤ 0
  · nlinarith
  replace hae := not_le.1 hae
  have hτ0 : 0 ≤ τ := le_trans (by nlinarith) hτ1
  have h1 : (a - ε / 2) * τ ≤ S := le_trans (by nlinarith) hS
  have h2 : (a - ε / 2) * ((1 - ε / 2) * O) ≤ (a - ε / 2) * τ :=
    mul_le_mul_of_nonneg_left hτ1 (by linarith)
  have h3 : (a - ε) * O ≤ (a - ε / 2) * ((1 - ε / 2) * O) := by
    have e1 := mul_nonneg (mul_nonneg hO hε.le) (show (0 : ℝ) ≤ 1 - a by linarith)
    have e2 := mul_nonneg (mul_nonneg hO hε.le) hε.le
    nlinarith
  linarith

theorem theorem_9' :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ (Ω : Type) [Fintype Ω] (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E),
      IsApproxOffline f k α μ Off →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ τ : ℝ, (1 - ε / 2) * optVal f k ≤ τ → τ ≤ optVal f k →
      ∀ σ : List E, IsStream σ →
      let p := ⌈4 / ε⌉₊
      (∀ ω, (alg1Out p f k α τ Off σ ω).card ≤ k) ∧
      (α / (1 + α) - ε) * optVal f k ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω) ∧
      (∀ L, L <+: σ → (alg1Stored (alg1Sets p f k α τ L) : ℝ) ≤ C * (k : ℝ) * ε⁻¹) ∧
      (∀ L e, L ++ [e] <+: σ → (alg1Queries p f k α τ L e : ℝ) ≤ C * ε⁻¹) := by
  refine ⟨5, by norm_num, ?_⟩
  intro E _ _ f hf0 hf k hk α hα0 hα1 Ω _ μ Off hOff ε hε hε1 τ hτ1 hτ2 σ hσ p
  obtain ⟨hp1, hp2, hp3⟩ := p_bounds ε hε hε1
  have hO := SSCommon.optVal_nonneg f hf0 k
  have hτ0 : 0 ≤ τ := le_trans (by nlinarith) hτ1
  obtain ⟨hst, hq, hval⟩ :=
    proposition_8 f hf0 hf k hk α hα0 hα1 μ Off hOff p hp1 τ hτ0 hτ2 σ hσ
  have hpR : (p : ℝ) ≤ 5 * ε⁻¹ := hp3
  have hεinv : 0 ≤ ε⁻¹ := inv_nonneg.2 hε.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    exact SSCommon.postProcess_card f k Off hOff.card_le ω _
      (SSCommon.alg1Sets_card p f k α τ σ)
  · have hS0 : 0 ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω) :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (hOff.prob_nonneg ω) (hf0 _)
    have ha : α / (1 + α) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have ha0 : 0 < α / (1 + α) := by positivity
    rw [add_comm α 1] at hval
    exact value_bound _ ε τ _ _ _ ha0 ha hε hε1 hO hτ1 hp2 hS0 hval
  · intro L hL
    have h := hst L hL
    have hk0 : (0 : ℝ) ≤ k := by positivity
    calc (alg1Stored (alg1Sets p f k α τ L) : ℝ) ≤ (p : ℝ) * k := by exact_mod_cast h
      _ ≤ 5 * ε⁻¹ * k := mul_le_mul_of_nonneg_right hpR hk0
      _ = 5 * (k : ℝ) * ε⁻¹ := by ring
  · intro L e hL
    have h := hq L e hL
    calc (alg1Queries p f k α τ L e : ℝ) ≤ p := by exact_mod_cast h
      _ ≤ 5 * ε⁻¹ := hpR

end SSThm9

open StreamSubmod NonmonotoneSubmod.Shared in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ (Ω : Type) [Fintype Ω] (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E),
      IsApproxOffline f k α μ Off →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ τ : ℝ, (1 - ε / 2) * optVal f k ≤ τ → τ ≤ optVal f k →
      ∀ σ : List E, IsStream σ →
      let p := ⌈4 / ε⌉₊
      (∀ ω, (alg1Out p f k α τ Off σ ω).card ≤ k) ∧
      (α / (1 + α) - ε) * optVal f k ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω) ∧
      (∀ L, L <+: σ → (alg1Stored (alg1Sets p f k α τ L) : ℝ) ≤ C * (k : ℝ) * ε⁻¹) ∧
      (∀ L e, L ++ [e] <+: σ → (alg1Queries p f k α τ L e : ℝ) ≤ C * ε⁻¹) :=
  SSThm9.theorem_9'
