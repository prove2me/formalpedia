-- Prove2me | solution 1 for SpikedWishart.FixedDim.eq_304
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:44:19.925328+00:00
-- url     : https://prove2.me/submissions/c2e12981-fae9-47a2-ab66-1d93c5ccf972

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_Model
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre
import Theorems.Thm_SpikedWishart_FixedDim_eq_302

set_option autoImplicit false

open MeasureTheory Set

namespace SWE304

open SpikedWishart.FixedDim

lemma prod_pairs (k : ℕ) (b : ℝ) :
    (∏ i : Fin k, ∏ j : Fin k, if i < j then b ^ 2 else 1) * b ^ k = b ^ (k ^ 2) := by
  have hpt : ∀ i j : Fin k,
      (if i < j then b else 1) * (if j < i then b else 1) * (if j = i then b else 1) = b := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne', not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne, not_lt.mpr h.le]
  have hdiag : ∏ i : Fin k, ∏ j : Fin k, (if j = i then b else 1) = b ^ k := by
    simp [Finset.prod_ite_eq']
  have hall : ∏ _i : Fin k, ∏ _j : Fin k, b = b ^ (k ^ 2) := by
    simp [Finset.prod_const, ← pow_mul, sq]
  have hcomm : (∏ i : Fin k, ∏ j : Fin k, if j < i then b else 1) =
      ∏ i : Fin k, ∏ j : Fin k, if i < j then b else 1 :=
    Finset.prod_comm
  calc (∏ i : Fin k, ∏ j : Fin k, if i < j then b ^ 2 else 1) * b ^ k
      = (∏ i : Fin k, ∏ j : Fin k, if i < j then b else 1) *
          (∏ i : Fin k, ∏ j : Fin k, if j < i then b else 1) *
          ∏ i : Fin k, ∏ j : Fin k, (if j = i then b else 1) := by
        rw [hdiag, hcomm, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        split_ifs <;> ring
    _ = ∏ _i : Fin k, ∏ _j : Fin k, b := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun j _ => hpt i j
    _ = b ^ (k ^ 2) := hall

lemma vandSq_affine {k : ℕ} (c b : ℝ) (ξ : Fin k → ℝ) :
    vandSq (fun j => c + b * ξ j) =
      (∏ i : Fin k, ∏ j : Fin k, if i < j then b ^ 2 else 1) * vandSq ξ := by
  unfold vandSq
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> ring

lemma cov {k : ℕ} (c : Fin k → ℝ) (b : ℝ) (hb : 0 < b) (F : (Fin k → ℝ) → ℝ) :
    ∫ y, F y = b ^ k * ∫ ξ, F (c + b • ξ) := by
  have h1 : ∫ ξ, F (c + b • ξ) = |(b ^ k)⁻¹| • ∫ z, F (c + z) := by
    have := Measure.integral_comp_smul (volume : Measure (Fin k → ℝ)) (fun z => F (c + z)) b
    rw [Module.finrank_fin_fun] at this
    exact this
  have h2 : ∫ z, F (c + z) = ∫ y, F y := integral_add_left_eq_self (μ := (volume : Measure (Fin k → ℝ))) (f := F) c
  have hbk : 0 < b ^ k := pow_pos hb k
  rw [h1, h2, smul_eq_mul, abs_of_pos (inv_pos.mpr hbk), ← mul_assoc, mul_inv_cancel₀ hbk.ne',
    one_mul]

lemma const_id (k d : ℕ) (π₁ s : ℝ) (hπ₁ : 0 < π₁) (hs : 0 < s) :
    (1 / (π₁ * s)) ^ (k ^ 2) * (π₁⁻¹) ^ (d * k) = 1 / (π₁ ^ (k * (k + d)) * s ^ (k ^ 2)) := by
  have e : k * (k + d) = k ^ 2 + d * k := by ring
  rw [e, pow_add, div_pow, one_pow, mul_pow, inv_pow]
  field_simp

lemma sqrt_pow (M k : ℕ) : Real.sqrt M ^ (k ^ 2) = (M : ℝ) ^ ((k : ℝ) ^ 2 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

lemma key (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) (x : ℝ) :
    ∫ y in Set.pi univ (fun _ : Fin k => Ioc 0 (1 / π₁ + x / (π₁ * Real.sqrt M))), w M π₁ y =
      Real.exp (-((k : ℝ) * M)) / (π₁ ^ (k * M) * (M : ℝ) ^ ((k : ℝ) ^ 2 / 2)) *
        ∫ ξ in Set.pi univ (fun _ : Fin k => Icc (-Real.sqrt M) x),
          vandSq ξ * ∏ j, Real.exp (-Real.sqrt M * ξ j) * (1 + ξ j / Real.sqrt M) ^ (M - k) := by
  obtain ⟨d, rfl⟩ : ∃ d, M = k + d := ⟨M - k, by omega⟩
  have hd : k + d - k = d := by omega
  rw [hd, ← sqrt_pow]
  set M := k + d with hMdef
  set s := Real.sqrt M with hs
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  have hs0 : 0 < s := Real.sqrt_pos.mpr hM
  have hss : s * s = M := Real.mul_self_sqrt hM.le
  set b : ℝ := 1 / (π₁ * s) with hb
  have hb0 : 0 < b := by positivity
  set c : Fin k → ℝ := fun _ => 1 / π₁ with hc
  set S := Set.pi univ (fun _ : Fin k => Ioc 0 (1 / π₁ + x / (π₁ * s))) with hS
  set T := Set.pi univ (fun _ : Fin k => Ioc (-s) x) with hT
  set f : (Fin k → ℝ) → ℝ := fun ξ =>
    vandSq ξ * ∏ j, Real.exp (-s * ξ j) * (1 + ξ j / s) ^ d with hf
  set P : ℝ := ∏ i : Fin k, ∏ j : Fin k, if i < j then b ^ 2 else 1 with hP
  have hmem : ∀ ξ : Fin k → ℝ, c + b • ξ ∈ S ↔ ξ ∈ T := by
    intro ξ
    simp only [hS, hT, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hc]
    refine forall_congr' fun j => ?_
    have e : 1 / π₁ + b * ξ j = (s + ξ j) / (π₁ * s) := by rw [hb]; field_simp
    have e2 : 1 / π₁ + x / (π₁ * s) = (s + x) / (π₁ * s) := by field_simp
    rw [e, e2, div_le_div_iff_of_pos_right (by positivity), div_pos_iff_of_pos_right (by positivity)]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hw : ∀ ξ : Fin k → ℝ, w M π₁ (c + b • ξ) =
      (Real.exp (-((k : ℝ) * M)) * (π₁⁻¹) ^ (d * k) * P) * f ξ := by
    intro ξ
    have hcb : (c + b • ξ) = fun j => 1 / π₁ + b * ξ j := by
      funext j; simp [hc]
    unfold w
    rw [hcb, vandSq_affine (1 / π₁) b ξ, hd]
    have hpt : ∀ j, Real.exp (-(M : ℝ) * π₁ * (1 / π₁ + b * ξ j)) * (1 / π₁ + b * ξ j) ^ d
        = (Real.exp (-(M : ℝ)) * (π₁⁻¹) ^ d) * (Real.exp (-s * ξ j) * (1 + ξ j / s) ^ d) := by
      intro j
      have e1 : -(M : ℝ) * π₁ * (1 / π₁ + b * ξ j) = -(M : ℝ) + -s * ξ j := by
        rw [hb, ← hss]; field_simp; ring
      have e2 : 1 / π₁ + b * ξ j = π₁⁻¹ * (1 + ξ j / s) := by rw [hb]; field_simp
      rw [e1, e2, Real.exp_add, mul_pow]; ring
    rw [Finset.prod_congr rfl fun j _ => hpt j, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul]
    have hex : Real.exp (-(M : ℝ)) ^ k = Real.exp (-((k : ℝ) * M)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [hex, hf]
    ring
  have hSm : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hTm : MeasurableSet T := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hae : T =ᵐ[volume] Set.pi univ (fun _ : Fin k => Icc (-s) x) := by
    rw [pi_univ_Icc, volume_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc
  have hind : ∀ ξ : Fin k → ℝ, S.indicator (w M π₁) (c + b • ξ) =
      T.indicator (fun ξ => (Real.exp (-((k : ℝ) * M)) * (π₁⁻¹) ^ (d * k) * P) * f ξ) ξ := by
    intro ξ
    by_cases h : ξ ∈ T
    · rw [Set.indicator_of_mem ((hmem ξ).mpr h), Set.indicator_of_mem h, hw]
    · rw [Set.indicator_of_notMem (fun h' => h ((hmem ξ).mp h')), Set.indicator_of_notMem h]
  calc ∫ y in S, w M π₁ y
      = ∫ y, S.indicator (w M π₁) y := (integral_indicator hSm).symm
    _ = b ^ k * ∫ ξ, S.indicator (w M π₁) (c + b • ξ) := cov c b hb0 _
    _ = b ^ k * ∫ ξ, T.indicator
          (fun ξ => (Real.exp (-((k : ℝ) * M)) * (π₁⁻¹) ^ (d * k) * P) * f ξ) ξ := by
        congr 1; exact integral_congr_ae (Filter.Eventually.of_forall hind)
    _ = b ^ k * ∫ ξ in T, (Real.exp (-((k : ℝ) * M)) * (π₁⁻¹) ^ (d * k) * P) * f ξ := by
        rw [integral_indicator hTm]
    _ = b ^ k * ((Real.exp (-((k : ℝ) * M)) * (π₁⁻¹) ^ (d * k) * P) *
          ∫ ξ in Set.pi univ (fun _ : Fin k => Icc (-s) x), f ξ) := by
        rw [integral_const_mul, setIntegral_congr_set hae]
    _ = Real.exp (-((k : ℝ) * M)) / (π₁ ^ (k * M) * s ^ (k ^ 2)) *
          ∫ ξ in Set.pi univ (fun _ : Fin k => Icc (-s) x), f ξ := by
        have hc' := const_id k d π₁ s hπ₁ hs0
        have hpp := prod_pairs k b
        have e : b ^ k * ((Real.exp (-((k : ℝ) * M)) * (π₁⁻¹) ^ (d * k) * P)) =
            Real.exp (-((k : ℝ) * M)) * ((P * b ^ k) * (π₁⁻¹) ^ (d * k)) := by ring
        rw [← mul_assoc, e, hpp, hb, hc', hMdef]
        ring

end SWE304

open SpikedWishart.FixedDim in
theorem eq304_of_eq302
    (H : ∀ (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) (t : ℝ),
      (sampleLaw M k).real {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ t} =
        (C M k π₁)⁻¹ * ∫ y in Set.pi univ (fun _ : Fin k => Ioc 0 t), w M π₁ y)
    (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) (x : ℝ)
    (hx : -Real.sqrt M ≤ x) :
    (sampleLaw M k).real
        {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ 1 / π₁ + x / (π₁ * Real.sqrt M)} =
      Real.exp (-((k : ℝ) * M)) / (π₁ ^ (k * M) * (M : ℝ) ^ ((k : ℝ) ^ 2 / 2) * C M k π₁) *
        ∫ ξ in Set.pi univ (fun _ : Fin k => Icc (-Real.sqrt M) x),
          vandSq ξ * ∏ j, Real.exp (-Real.sqrt M * ξ j) * (1 + ξ j / Real.sqrt M) ^ (M - k) := by
  rw [H k M hk hkM π₁ hπ₁, SWE304.key k M hk hkM π₁ hπ₁ x]
  ring

open SpikedWishart.FixedDim in
theorem solution (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) (x : ℝ)
    (hx : -Real.sqrt M ≤ x) :
    (sampleLaw M k).real
        {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ 1 / π₁ + x / (π₁ * Real.sqrt M)} =
      Real.exp (-((k : ℝ) * M)) / (π₁ ^ (k * M) * (M : ℝ) ^ ((k : ℝ) ^ 2 / 2) * C M k π₁) *
        ∫ ξ in Set.pi univ (fun _ : Fin k => Icc (-Real.sqrt M) x),
          vandSq ξ * ∏ j, Real.exp (-Real.sqrt M * ξ j) * (1 + ξ j / Real.sqrt M) ^ (M - k) := by
  exact eq304_of_eq302 SpikedWishart.FixedDim.eq_302 k M hk hkM π₁ hπ₁ x hx
