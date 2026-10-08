-- Prove2me | solution 1 for SmoothedSimplex.Shadow.combination_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:08:59.195971+00:00
-- url     : https://prove2.me/submissions/4c9b924b-9ea2-4149-9965-8e2f880586ef

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
/-- Pointwise dyadic bound: `min 1 ((t / f)^2)`-type estimate. -/
theorem c3bf2c4f_real_aux (t f : ℝ) (k : ℕ) (hf : 0 < f) (hk : t * 2 ^ (k + 1) ≤ f)
    (ht : 0 ≤ t) : (t / f) ^ 2 ≤ (1 / 4 : ℝ) ^ (k + 1) := by
  have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have h1 : t / f ≤ 1 / 2 ^ (k + 1) := by
    rw [div_le_div_iff₀ hf h2]; linarith
  have h3 : (1 / 4 : ℝ) ^ (k + 1) = (1 / 2 ^ (k + 1)) ^ 2 := by
    rw [div_pow, div_pow, one_pow, one_pow, ← pow_mul, mul_comm (k + 1) 2, pow_mul]; norm_num
  rw [h3]
  exact pow_le_pow_left₀ (div_nonneg ht hf.le) h1 2

theorem c3bf2c4f_real_aux2 (a : ℝ) (k : ℕ) :
    (1 / 4 : ℝ) ^ (k + 1) * (a * 2 ^ (k + 2)) = a * (1 / 2) ^ k := by
  have h : (1 / 4 : ℝ) ^ (k + 1) * 2 ^ (k + 2) = (1 / 2) ^ k := by
    have e1 : (1 / 4 : ℝ) ^ (k + 1) = (1 / 2) ^ k * (1 / 2) ^ k * (1 / 4) := by
      rw [pow_succ, ← mul_pow]; norm_num
    have e2 : (2 : ℝ) ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
    have e3 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [e1, e2]
    calc (1 / 2 : ℝ) ^ k * (1 / 2) ^ k * (1 / 4) * (2 ^ k * 4)
        = (1 / 2) ^ k * ((1 / 2) ^ k * 2 ^ k) := by ring
      _ = (1 / 2) ^ k := by rw [e3, mul_one]
  calc (1 / 4 : ℝ) ^ (k + 1) * (a * 2 ^ (k + 2))
      = a * ((1 / 4 : ℝ) ^ (k + 1) * 2 ^ (k + 2)) := by ring
    _ = a * (1 / 2) ^ k := by rw [h]

open MeasureTheory ProbabilityTheory in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν] (κ : Kernel X Y) [IsMarkovKernel κ]
    (F : X → ℝ) (G : X → Y → ℝ) (hF : Measurable F) (hG : Measurable (Function.uncurry G))
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x y, 0 ≤ G x y) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : ∀ ε : ℝ, 0 ≤ ε → (ν ⊗ₘ κ) {p | F p.1 ≤ ε} ≤ ENNReal.ofReal (α * ε))
    (h2 : ∀ ε : ℝ, 0 ≤ ε → ∀ x, κ x {y | G x y ≤ ε} ≤ ENNReal.ofReal ((β * ε) ^ 2)) :
    ∀ ε : ℝ, 0 ≤ ε →
      (ν ⊗ₘ κ) {p | F p.1 * G p.1 p.2 ≤ ε} ≤ ENNReal.ofReal (4 * α * β * ε) := by
  intro ε hε
  set t := β * ε with ht_def
  have ht : 0 ≤ t := mul_nonneg hβ hε
  -- marginal bound
  have hν : ∀ s, 0 ≤ s → ν {x | F x ≤ s} ≤ ENNReal.ofReal (α * s) := by
    intro s hs
    have hmeas : MeasurableSet {x | F x ≤ s} := measurableSet_le hF measurable_const
    have e : (ν ⊗ₘ κ).fst {x | F x ≤ s} = (ν ⊗ₘ κ) (Prod.fst ⁻¹' {x | F x ≤ s}) :=
      Measure.fst_apply hmeas
    rw [Measure.fst_compProd] at e
    rw [e]
    exact h1 s hs
  have hS : MeasurableSet {p : X × Y | F p.1 * G p.1 p.2 ≤ ε} := by
    have hm : Measurable (fun p : X × Y => F p.1 * G p.1 p.2) :=
      (hF.comp measurable_fst).mul hG
    exact measurableSet_le hm measurable_const
  rw [Measure.compProd_apply hS]
  set A : Set X := {x | F x ≤ 2 * t} with hA
  set B : ℕ → Set X := fun k => {x | F x ≤ t * 2 ^ (k + 2)} with hB
  have hAm : MeasurableSet A := measurableSet_le hF measurable_const
  have hBm : ∀ k, MeasurableSet (B k) := fun k => measurableSet_le hF measurable_const
  set w : ℕ → ENNReal := fun k => ENNReal.ofReal ((1 / 4 : ℝ) ^ (k + 1)) with hw
  set R : X → ENNReal := fun x =>
    A.indicator (fun _ => (1 : ENNReal)) x + ∑' k, (B k).indicator (fun _ => w k) x with hR
  have hpt : ∀ x, κ x (Prod.mk x ⁻¹' {p : X × Y | F p.1 * G p.1 p.2 ≤ ε}) ≤ R x := by
    intro x
    by_cases hx : F x ≤ 2 * t
    · calc κ x _ ≤ 1 := prob_le_one
        _ = A.indicator (fun _ => (1 : ENNReal)) x := by
          rw [Set.indicator_of_mem (show x ∈ A from hx)]
        _ ≤ R x := le_self_add
    · push Not at hx
      have hFpos : 0 < F x := by linarith
      have hsub : Prod.mk x ⁻¹' {p : X × Y | F p.1 * G p.1 p.2 ≤ ε}
          ⊆ {y | G x y ≤ ε / F x} := by
        intro y hy
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy ⊢
        rw [le_div_iff₀ hFpos]; linarith [mul_comm (F x) (G x y)]
      calc κ x _ ≤ κ x {y | G x y ≤ ε / F x} := measure_mono hsub
        _ ≤ ENNReal.ofReal ((β * (ε / F x)) ^ 2) := h2 _ (div_nonneg hε hFpos.le) x
        _ ≤ R x := by
          have hbe : β * (ε / F x) = t / F x := by rw [ht_def, mul_div_assoc]
          rw [hbe]
          rcases ht.lt_or_eq with htpos | ht0
          · have hex : ∃ k : ℕ, F x ≤ t * 2 ^ (k + 2) := by
              obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (F x / t) (by norm_num : (1 : ℝ) < 2)
              refine ⟨n, ?_⟩
              rw [div_lt_iff₀ htpos] at hn
              have : (2 : ℝ) ^ n ≤ 2 ^ (n + 2) :=
                pow_le_pow_right₀ (by norm_num) (by omega)
              nlinarith
            classical
            set k := Nat.find hex with hk
            have hkspec : F x ≤ t * 2 ^ (k + 2) := Nat.find_spec hex
            have hklow : t * 2 ^ (k + 1) ≤ F x := by
              rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hs
              · rw [h0]; norm_num; linarith
              · have hmin := Nat.find_min hex (show k - 1 < k by omega)
                push Not at hmin
                have : k - 1 + 2 = k + 1 := by omega
                rw [this] at hmin
                exact hmin.le
            calc ENNReal.ofReal ((t / F x) ^ 2) ≤ w k :=
                  ENNReal.ofReal_le_ofReal (c3bf2c4f_real_aux t (F x) k hFpos hklow ht)
              _ = (B k).indicator (fun _ => w k) x := by
                  rw [Set.indicator_of_mem (show x ∈ B k from hkspec)]
              _ ≤ ∑' j, (B j).indicator (fun _ => w j) x :=
                  ENNReal.le_tsum (f := fun j => (B j).indicator (fun _ => w j) x) k
              _ ≤ R x := le_add_self
          · rw [← ht0]; simp
  have hRint : ∫⁻ x, R x ∂ν = ν A + ∑' k, w k * ν (B k) := by
    rw [hR]
    rw [lintegral_add_left (measurable_const.indicator hAm)]
    rw [lintegral_tsum (fun k => (measurable_const.indicator (hBm k)).aemeasurable)]
    simp only [lintegral_indicator_const hAm, lintegral_indicator_const (hBm _), one_mul]
  calc ∫⁻ x, κ x (Prod.mk x ⁻¹' {p : X × Y | F p.1 * G p.1 p.2 ≤ ε}) ∂ν
      ≤ ∫⁻ x, R x ∂ν := lintegral_mono hpt
    _ = ν A + ∑' k, w k * ν (B k) := hRint
    _ ≤ ENNReal.ofReal (α * (2 * t)) + ∑' k : ℕ, ENNReal.ofReal (α * t * (1 / 2) ^ k) := by
        gcongr with k
        · exact hν _ (by linarith)
        · calc w k * ν (B k) ≤ w k * ENNReal.ofReal (α * (t * 2 ^ (k + 2))) :=
                by gcongr; exact hν _ (by positivity)
            _ = ENNReal.ofReal (α * t * (1 / 2) ^ k) := by
                rw [hw, ← ENNReal.ofReal_mul (by positivity)]
                congr 1
                rw [← c3bf2c4f_real_aux2 (α * t) k]; ring
    _ = ENNReal.ofReal (4 * α * β * ε) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          ((summable_geometric_two).mul_left (α * t))]
        rw [tsum_mul_left, tsum_geometric_two, ← ENNReal.ofReal_add (by positivity)
          (by positivity), ht_def]
        congr 1; ring
