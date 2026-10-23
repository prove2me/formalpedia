-- Prove2me | solution 1 for StaticReusable.Guarantee.service_ratio_eq_R
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:46:48.632612+00:00
-- url     : https://prove2.me/submissions/58bc2f32-277d-459f-a11e-4bf2609d9845

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace SolSRGRatioR
open StaticReusable.Guarantee

lemma weight_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ)
    (i : ℕ) : 0 ≤ weight C μ lam i := by
  unfold weight
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have := (hlam j (by simp only [Finset.mem_Icc]; omega)).1
  positivity

lemma weight_C_pos {C : ℕ} {μ : ℝ} (lam : ℕ → ℝ) : 0 < weight C μ lam C := by
  unfold weight
  have : Finset.Icc (C + 1) C = ∅ := by ext; simp
  rw [this, Finset.prod_empty, mul_one]
  exact_mod_cast Nat.descFactorial_self C ▸ Nat.factorial_pos C

lemma total_pos {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ) :
    0 < ∑ k ∈ Finset.range (C + 1), weight C μ lam k := by
  have h := Finset.single_le_sum (f := fun k => weight C μ lam k)
    (fun k _ => weight_nonneg hμ hlam k) (Finset.self_mem_range_succ C)
  linarith [weight_C_pos (C := C) (μ := μ) lam]

lemma zExt_zOf {C : ℕ} {μ : ℝ} (lam : ℕ → ℝ) (k : ℕ) (hk : k ≤ C + 1) :
    zExt C (zOf C μ lam) k = zOf C μ lam k := by
  unfold zExt
  split_ifs with h
  · rfl
  · have : k = C + 1 := by omega
    subst this
    unfold zOf
    have : Finset.Icc (C + 1) C = ∅ := by ext; simp
    rw [this, Finset.prod_empty]

lemma weight_eq {C : ℕ} {μ : ℝ} (lam : ℕ → ℝ) (i : ℕ) (hi : i ≤ C) :
    weight C μ lam i = a C i * zExt C (zOf C μ lam) (i + 1) := by
  rw [zExt_zOf lam (i + 1) (by omega)]
  rfl

lemma zOf_succ {C : ℕ} {μ : ℝ} (hμ : 0 < μ) (lam : ℕ → ℝ) (i : ℕ) (hi : i ≤ C) :
    lam i * zOf C μ lam (i + 1) = μ * zOf C μ lam i := by
  unfold zOf
  have hI : Finset.Icc (i + 1) C = Finset.Ioc i C := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [Finset.Icc_eq_cons_Ioc hi, Finset.prod_cons, hI]
  field_simp

lemma weight_const {C : ℕ} {μ : ℝ} (l : ℝ) (i : ℕ) :
    weight C μ (fun _ => l) i = a C i * (l / μ) ^ (C - i) := by
  unfold weight
  rw [Finset.prod_const, Nat.card_Icc, show C + 1 - (i + 1) = C - i by omega]
  rfl

end SolSRGRatioR

open SolSRGRatioR in
theorem solution {C : ℕ} {μ Λ : ℝ} (hC : 1 ≤ C) (hμ : 0 < μ)
    (lam : ℕ → ℝ) (hlam : lam ∈ StaticReusable.Guarantee.Policies C Λ) :
    StaticReusable.Guarantee.serviceLevel C μ
        (fun _ => StaticReusable.Guarantee.staticRate C μ lam) /
        StaticReusable.Guarantee.serviceLevel C μ lam =
      StaticReusable.Guarantee.R C (StaticReusable.Guarantee.zOf C μ lam) := by
  open StaticReusable.Guarantee in
  set z := zOf C μ lam with hz
  have hT := total_pos hμ hlam
  have hTeq : ∑ k ∈ Finset.range (C + 1), weight C μ lam k =
      ∑ k ∈ Finset.range (C + 1), a C k * zExt C z (k + 1) := by
    apply Finset.sum_congr rfl; intro k hk
    exact weight_eq lam k (by simp at hk; omega)
  set T := ∑ k ∈ Finset.range (C + 1), weight C μ lam k with hTdef
  have hSL : serviceLevel C μ lam = xSum C z / T := by
    unfold serviceLevel prob xSum
    rw [← Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl; intro k hk
    exact weight_eq lam k (by simp at hk; omega)
  have hMS : marketShare C μ lam = μ * uSum C z / T := by
    unfold marketShare prob uSum
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [weight_eq lam k (by omega), zExt_zOf lam (k + 1) (by omega),
      zExt_zOf lam k (by omega)]
    have := zOf_succ hμ lam k hk.2
    rw [← hz] at this ⊢
    rw [← hTdef, mul_div_assoc', div_left_inj' hT.ne']
    calc lam k * (a C k * z (k + 1)) = a C k * (lam k * z (k + 1)) := by ring
      _ = μ * (a C k * z k) := by rw [this]; ring
  have hrate : staticRate C μ lam / μ = uSum C z / xSum C z := by
    unfold staticRate
    change marketShare C μ lam / serviceLevel C μ lam / μ = _
    rw [hMS, hSL]
    field_simp
  have hSLs : serviceLevel C μ (fun _ => staticRate C μ lam) =
      (∑ i ∈ Finset.Icc 1 C, a C i * (uSum C z / xSum C z) ^ (C - i)) /
        ∑ i ∈ Finset.range (C + 1), a C i * (uSum C z / xSum C z) ^ (C - i) := by
    unfold serviceLevel prob
    rw [← Finset.sum_div]
    simp only [weight_const, hrate]
  rw [hSLs, hSL, div_div_div_eq]
  unfold R
  rw [← hTeq]
  ring
