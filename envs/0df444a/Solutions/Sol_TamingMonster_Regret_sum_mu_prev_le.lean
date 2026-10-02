-- Prove2me | solution 1 for TamingMonster.Regret.sum_mu_prev_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:54:04.99899+00:00
-- url     : https://prove2.me/submissions/05bb33f3-f40b-4859-b4e0-af7e7bf304fb

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

set_option autoImplicit false

namespace TamingMonster.Regret

open MeasureTheory

open MeasureTheory in
theorem p79_epoch_spec (τ : ℕ → ℕ) (hτ : StrictMono τ) (t : ℕ) :
    t ≤ τ (epochOf τ t) :=
  Nat.sInf_mem (s := {m : ℕ | t ≤ τ m}) ⟨t, hτ.id_le t⟩

open MeasureTheory in
theorem p79_epoch_le (τ : ℕ → ℕ) (t m : ℕ) (h : t ≤ τ m) : epochOf τ t ≤ m :=
  Nat.sInf_le (s := {m : ℕ | t ≤ τ m}) h

open MeasureTheory in
theorem p79_epoch_pos (τ : ℕ → ℕ) (hτ : StrictMono τ) (hτ0 : τ 0 = 0) (t : ℕ) (ht : 1 ≤ t) :
    1 ≤ epochOf τ t := by
  by_contra h
  have h0 : epochOf τ t = 0 := by omega
  have := p79_epoch_spec τ hτ t
  rw [h0, hτ0] at this
  omega

open MeasureTheory in
theorem p79_epoch_prev_lt (τ : ℕ → ℕ) (hτ : StrictMono τ) (hτ0 : τ 0 = 0) (t : ℕ) (ht : 1 ≤ t) :
    τ (epochOf τ t - 1) < t := by
  by_contra h
  push Not at h
  have h1 := p79_epoch_le τ t _ h
  have h2 := p79_epoch_pos τ hτ hτ0 t ht
  omega

open MeasureTheory in
theorem p79_sum_inv_sqrt_le (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt (t : ℝ) ≤ 2 * Real.sqrt (T : ℝ) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hb : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hab : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    have ha2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have key : 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 * Real.sqrt (n : ℝ) := by
      rw [div_le_iff₀ hb]
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab)]
    linarith

open MeasureTheory in
theorem p79_main {X : Type*} {K : ℕ} [NeZero K] (Pi : Finset (X → Fin K))
    (hPi : Pi.Nonempty) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (τ : ℕ → ℕ) (hτ0 : τ 0 = 0) (hτ : StrictMono τ)
    (hτ2 : ∀ m, 1 ≤ m → τ (m + 1) ≤ 2 * τ m) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t - 1) ≤
      (τ (m0 Pi δ τ) : ℝ) / (2 * (K : ℝ))
        + Real.sqrt (8 * dT Pi δ (τ (epochOf τ T)) * (τ (epochOf τ T) : ℝ) / (K : ℝ)) := by
  have hK : (0 : ℝ) < (K : ℝ) := by
    have : K ≠ 0 := NeZero.ne K
    exact_mod_cast Nat.pos_of_ne_zero this
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    simp only [Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.sum_empty]
    positivity
  set M := epochOf τ T with hMdef
  set D := dT Pi δ (τ M) with hDdef
  have hTM : T ≤ τ M := p79_epoch_spec τ hτ T
  have hM1 : 1 ≤ M := p79_epoch_pos τ hτ hτ0 T hT
  have hcard : (1 : ℝ) ≤ (Pi.card : ℝ) := by exact_mod_cast hPi.card_pos
  -- d is positive and monotone on t ≥ 1
  have hdpos : ∀ a : ℕ, 1 ≤ a → 0 < dT Pi δ a := by
    intro a ha
    unfold dT
    apply Real.log_pos
    have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    rw [lt_div_iff₀ hδ0]
    nlinarith [mul_le_mul ha' ha' (by norm_num) (by positivity)]
  have hdmono : ∀ a b : ℕ, 1 ≤ a → a ≤ b → dT Pi δ a ≤ dT Pi δ b := by
    intro a b ha hab
    unfold dT
    have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    apply Real.log_le_log
    · apply div_pos _ hδ0; positivity
    · apply div_le_div_of_nonneg_right _ hδ0.le
      have : (a : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 := by nlinarith
      nlinarith
  have hτM1 : (1 : ℝ) ≤ (τ M : ℝ) := by exact_mod_cast (le_trans hT hTM)
  have hD : 0 < D := hdpos _ (le_trans hT hTM)
  have hμle : ∀ m, muM Pi δ τ m ≤ 1 / (2 * (K : ℝ)) := by
    intro m; unfold muM; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hμsq : ∀ m, 1 ≤ m →
      muM Pi δ τ m ≤ Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ))) := by
    intro m hm; unfold muM; rw [if_neg (by omega)]; exact min_le_right _ _
  have hRHSsqrt : 0 ≤ Real.sqrt (8 * D * (τ M : ℝ) / (K : ℝ)) := Real.sqrt_nonneg _
  by_cases hS : ∃ m, 1 ≤ m ∧ dT Pi δ (τ m) / (τ m : ℝ) ≤ 1 / (4 * (K : ℝ))
  · -- m0 is a genuine member
    have hm0mem : 1 ≤ m0 Pi δ τ ∧
        dT Pi δ (τ (m0 Pi δ τ)) / (τ (m0 Pi δ τ) : ℝ) ≤ 1 / (4 * (K : ℝ)) :=
      Nat.sInf_mem (s := {m : ℕ | 1 ≤ m ∧ dT Pi δ (τ m) / (τ m : ℝ) ≤ 1 / (4 * (K : ℝ))}) hS
    have hm01 := hm0mem.1
    set m₀ := m0 Pi δ τ with hm0def
    have hterm : ∀ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t - 1) ≤
        (if t ≤ τ m₀ then 1 / (2 * (K : ℝ)) else 0)
          + Real.sqrt (2 * D / (K : ℝ)) * (1 / Real.sqrt (t : ℝ)) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      have hsq0 : 0 ≤ Real.sqrt (2 * D / (K : ℝ)) * (1 / Real.sqrt (t : ℝ)) := by positivity
      split_ifs with htm
      · linarith [hμle (epochOf τ t - 1)]
      · push Not at htm
        have hem : m₀ < epochOf τ t := by
          by_contra h
          push Not at h
          have := le_trans (p79_epoch_spec τ hτ t) (hτ.monotone h)
          omega
        set m' := epochOf τ t - 1 with hm'
        have hm'1 : 1 ≤ m' := by omega
        have hτm'pos : 1 ≤ τ m' := by
          have := hτ (show 0 < m' by omega); omega
        have hlt : τ m' < t := p79_epoch_prev_lt τ hτ hτ0 t ht.1
        have h2 : t ≤ 2 * τ m' := by
          have h1 := p79_epoch_spec τ hτ t
          have h3 := hτ2 m' hm'1
          have : m' + 1 = epochOf τ t := by omega
          rw [this] at h3
          omega
        have hdle : dT Pi δ (τ m') ≤ D := hdmono _ _ hτm'pos (by omega)
        have hd0 : 0 < dT Pi δ (τ m') := hdpos _ hτm'pos
        have ht' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.1
        have hτ' : (1 : ℝ) ≤ (τ m' : ℝ) := by exact_mod_cast hτm'pos
        have h2' : (t : ℝ) ≤ 2 * (τ m' : ℝ) := by exact_mod_cast h2
        have hrw : Real.sqrt (2 * D / (K : ℝ)) * (1 / Real.sqrt (t : ℝ)) =
            Real.sqrt (2 * D / ((K : ℝ) * (t : ℝ))) := by
          rw [mul_one_div, ← Real.sqrt_div (by positivity)]
          congr 1
          field_simp
        rw [hrw, zero_add]
        refine le_trans (hμsq m' hm'1) (Real.sqrt_le_sqrt ?_)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have e1 : dT Pi δ (τ m') * ((K : ℝ) * (t : ℝ)) ≤ D * ((K : ℝ) * (t : ℝ)) :=
          mul_le_mul_of_nonneg_right hdle (by positivity)
        have e2 : D * ((K : ℝ) * (t : ℝ)) ≤ D * ((K : ℝ) * (2 * (τ m' : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2' hK.le) hD.le
        nlinarith
    have hsum1 := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum1
    have hcnt : ∑ t ∈ Finset.Icc 1 T, (if t ≤ τ m₀ then 1 / (2 * (K : ℝ)) else 0) ≤
        (τ m₀ : ℝ) / (2 * (K : ℝ)) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hsub : (Finset.Icc 1 T).filter (fun t => t ≤ τ m₀) ⊆ Finset.Icc 1 (τ m₀) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
        omega
      have hc := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hc
      have hc' : (((Finset.Icc 1 T).filter (fun t => t ≤ τ m₀)).card : ℝ) ≤ (τ m₀ : ℝ) := by
        exact_mod_cast (show _ ≤ τ m₀ by omega)
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hc' (by positivity)
    have hinv := p79_sum_inv_sqrt_le T
    have hfin : Real.sqrt (2 * D / (K : ℝ)) * ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt (t : ℝ) ≤
        Real.sqrt (8 * D * (τ M : ℝ) / (K : ℝ)) := by
      refine le_trans (mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _)) ?_
      have hT' : (T : ℝ) ≤ (τ M : ℝ) := by exact_mod_cast hTM
      have hl0 : 0 ≤ Real.sqrt (2 * D / (K : ℝ)) * (2 * Real.sqrt (T : ℝ)) := by positivity
      calc Real.sqrt (2 * D / (K : ℝ)) * (2 * Real.sqrt (T : ℝ))
          = Real.sqrt ((Real.sqrt (2 * D / (K : ℝ)) * (2 * Real.sqrt (T : ℝ))) ^ 2) :=
            (Real.sqrt_sq hl0).symm
        _ ≤ Real.sqrt (8 * D * (τ M : ℝ) / (K : ℝ)) := by
            apply Real.sqrt_le_sqrt
            rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hK]
            nlinarith
    linarith
  · -- no admissible epoch: every μ is 1/(2K), and d_{τ_M}/τ_M > 1/(4K)
    have hnot : ¬ (dT Pi δ (τ M) / (τ M : ℝ) ≤ 1 / (4 * (K : ℝ))) := fun h => hS ⟨M, hM1, h⟩
    push Not at hnot
    have hD' : (τ M : ℝ) < D * (4 * (K : ℝ)) := by
      have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < (τ M : ℝ))).mp hnot
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)] at h
      exact h
    have hsum : ∑ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t - 1) ≤ (T : ℝ) / (2 * (K : ℝ)) := by
      calc ∑ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t - 1)
          ≤ ∑ t ∈ Finset.Icc 1 T, 1 / (2 * (K : ℝ)) := Finset.sum_le_sum (fun t _ => hμle _)
        _ = (T : ℝ) / (2 * (K : ℝ)) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            simp [div_eq_mul_inv]
    have hT' : (T : ℝ) ≤ (τ M : ℝ) := by exact_mod_cast hTM
    have hsq : (T : ℝ) / (2 * (K : ℝ)) ≤ Real.sqrt (8 * D * (τ M : ℝ) / (K : ℝ)) := by
      have hl0 : 0 ≤ (T : ℝ) / (2 * (K : ℝ)) := by positivity
      calc (T : ℝ) / (2 * (K : ℝ)) = Real.sqrt (((T : ℝ) / (2 * (K : ℝ))) ^ 2) :=
            (Real.sqrt_sq hl0).symm
        _ ≤ Real.sqrt (8 * D * (τ M : ℝ) / (K : ℝ)) := by
            apply Real.sqrt_le_sqrt
            rw [div_pow, div_le_div_iff₀ (by positivity) hK]
            have hTT : (T : ℝ) ^ 2 ≤ (τ M : ℝ) ^ 2 := by
              have : (0 : ℝ) ≤ T := by positivity
              nlinarith
            nlinarith [mul_pos hK hK, mul_le_mul_of_nonneg_left hD'.le
              (show (0 : ℝ) ≤ (τ M : ℝ) * ((2 * (K : ℝ)) ^ 2) by positivity)]
    have hm0nn : 0 ≤ (τ (m0 Pi δ τ) : ℝ) / (2 * (K : ℝ)) := by positivity
    linarith

end TamingMonster.Regret

open MeasureTheory TamingMonster.Regret in
theorem solution {X : Type*} {K : ℕ} [NeZero K] (Pi : Finset (X → Fin K))
    (hPi : Pi.Nonempty) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (τ : ℕ → ℕ) (hτ0 : τ 0 = 0) (hτ : StrictMono τ)
    (hτ2 : ∀ m, 1 ≤ m → τ (m + 1) ≤ 2 * τ m) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t - 1) ≤
      (τ (m0 Pi δ τ) : ℝ) / (2 * (K : ℝ))
        + Real.sqrt (8 * dT Pi δ (τ (epochOf τ T)) * (τ (epochOf τ T) : ℝ) / (K : ℝ)) := by
  exact TamingMonster.Regret.p79_main Pi hPi δ hδ0 hδ1 τ hτ0 hτ hτ2 T
