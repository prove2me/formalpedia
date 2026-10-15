-- Prove2me | solution 1 for OffloadGNEP.Mono.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T22:10:43.590462+00:00
-- url     : https://prove2.me/submissions/a82ef1f6-9c41-4af2-a424-2e9af5308c18

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

set_option autoImplicit false

open OffloadGNEP.Mono

lemma offl_sum_tier (f : Tier → ℝ) : ∑ i, f i = f .m + f .clet + f .cloud := by
  have h : (Finset.univ : Finset Tier) = {Tier.m, Tier.clet, Tier.cloud} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma offl_core {N : ℕ} (hN : 0 < N) (d z : Fin N → ℝ) (a a' c : ℝ)
    (ha : 0 < a) (ha' : 0 < a') (hc : 0 < c)
    (hz0 : ∀ u, 0 ≤ z u) (hzc : ∀ u, z u ≤ c)
    (h1 : a * (N * c) ≤ 1) (h2 : a' * (N * c) ≤ 1) :
    0 ≤ (∑ u, d u) ^ 2 * (a * a') + (a ^ 2 + a' ^ 2) / 2 * ∑ u, d u ^ 2
      + (∑ u, d u) * (a * a' * (a + a')) * ∑ u, d u * z u := by
  have hz : ∑ u, z u ≤ N * c := by
    calc ∑ u, z u ≤ ∑ _u : Fin N, c := Finset.sum_le_sum fun u _ => hzc u
      _ = N * c := by simp
  have hzd : ∑ u, z u * d u ^ 2 ≤ c * ∑ u, d u ^ 2 := by
    calc ∑ u, z u * d u ^ 2 ≤ ∑ u, c * d u ^ 2 :=
          Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (hzc u) (sq_nonneg _)
      _ = c * ∑ u, d u ^ 2 := by rw [Finset.mul_sum]
  have hQ0 : 0 ≤ ∑ u, d u ^ 2 := Finset.sum_nonneg fun u _ => sq_nonneg _
  have hnn : 0 ≤ ∑ u, z u * ((∑ v, d v) + d u) ^ 2 :=
    Finset.sum_nonneg fun u _ => mul_nonneg (hz0 u) (sq_nonneg _)
  have hexp : ∑ u, z u * ((∑ v, d v) + d u) ^ 2
      = (∑ v, d v) ^ 2 * ∑ u, z u + 2 * (∑ v, d v) * ∑ u, d u * z u
        + ∑ u, z u * d u ^ 2 := by
    have : ∀ u, z u * ((∑ v, d v) + d u) ^ 2
        = (∑ v, d v) ^ 2 * z u + 2 * (∑ v, d v) * (d u * z u) + z u * d u ^ 2 :=
      fun u => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hSR : -((∑ v, d v) ^ 2 * (N * c) + c * ∑ u, d u ^ 2)
      ≤ 2 * (∑ v, d v) * ∑ u, d u * z u := by
    have := mul_le_mul_of_nonneg_left hz (sq_nonneg (∑ v, d v))
    linarith
  have hk1 : (a + a') * (N * c) ≤ 2 := by
    have := add_mul a a' ((N : ℝ) * c); linarith
  have hNc : c ≤ N * c := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hk2 : (a + a') * c ≤ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hNc (add_pos ha ha').le]
  have hp : 0 ≤ a * a' * (a + a') := by positivity
  have h3 := mul_le_mul_of_nonneg_left hSR hp
  have h4 : (a * a' * (a + a')) * ((∑ v, d v) ^ 2 * (N * c) + c * ∑ u, d u ^ 2)
      ≤ (a * a') * (2 * (∑ v, d v) ^ 2 + 2 * ∑ u, d u ^ 2) := by
    have e : (a * a' * (a + a')) * ((∑ v, d v) ^ 2 * (N * c) + c * ∑ u, d u ^ 2)
        = a * a' * ((∑ v, d v) ^ 2 * ((a + a') * (N * c)) + (∑ u, d u ^ 2) * ((a + a') * c)) := by
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hk1 (sq_nonneg (∑ v, d v)),
      mul_le_mul_of_nonneg_left hk2 hQ0]
  have h5 : a * a' * ∑ u, d u ^ 2 ≤ (a ^ 2 + a' ^ 2) / 2 * ∑ u, d u ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (a - a')) hQ0]
  nlinarith [h3, h4, h5]

lemma offl_mpart (α p q : ℝ) (_hα : 0 < α) (hp : α * p < 1) (hq : α * q < 1) :
    0 ≤ (α / (1 - α * q) ^ 2 - α / (1 - α * p) ^ 2) * (q - p) := by
  have hu : 0 < 1 - α * p := by linarith
  have hv : 0 < 1 - α * q := by linarith
  have e : (α / (1 - α * q) ^ 2 - α / (1 - α * p) ^ 2) * (q - p)
      = ((1 - α * p) - (1 - α * q)) ^ 2 * ((1 - α * p) + (1 - α * q))
        / ((1 - α * p) ^ 2 * (1 - α * q) ^ 2) := by
    field_simp
    ring
  rw [e]
  positivity

lemma offl_load_eq {N : ℕ} (P : Params N) (x : Fin N → Tier → ℝ) :
    load P x = ∑ u, P.delta u * x u .clet / (P.n : ℝ) := by
  unfold load
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

lemma offl_T {N : ℕ} (P : Params N) (x : Fin N → Tier → ℝ) (u : Fin N) :
    1 - (1 / (P.n : ℝ)) * ∑ v ∈ Finset.univ.erase u, P.delta v * x v .clet
      = (1 - load P x) + P.delta u * x u .clet / (P.n : ℝ) := by
  have h := Finset.add_sum_erase Finset.univ (fun v => P.delta v * x v .clet) (Finset.mem_univ u)
  unfold load
  rw [← h]
  ring

lemma offl_mem {N : ℕ} (P : Params N) (x : Fin N → Tier → ℝ) (hx : x ∈ K P) (u : Fin N) :
    0 ≤ x u .m ∧ x u .m ≤ 1 ∧ 0 ≤ x u .clet ∧ x u .clet ≤ P.chi := by
  obtain ⟨h1, h2, h3, h4⟩ := hx.1 u
  have a1 := h1 .m
  have a2 := h1 .clet
  have a3 := h1 .cloud
  exact ⟨a1, by linarith, a2, by linarith⟩

lemma offl_clet_alg (δ n Dx Dy xc yc β : ℝ) (hn : n ≠ 0) (hDx : Dx ≠ 0) (hDy : Dy ≠ 0) :
    (β + δ * (Dy + δ * yc / n) / Dy ^ 2 - (β + δ * (Dx + δ * xc / n) / Dx ^ 2)) * (yc - xc)
    = n * ((δ * yc / n - δ * xc / n) * (1 / Dy - 1 / Dx)
        + ((1 / Dx) ^ 2 + (1 / Dy) ^ 2) / 2 * (δ * yc / n - δ * xc / n) ^ 2
        + ((1 / Dy) ^ 2 - (1 / Dx) ^ 2)
          * ((δ * yc / n - δ * xc / n) * ((δ * xc / n + δ * yc / n) / 2))) := by
  field_simp
  ring

open OffloadGNEP.Mono in
theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (h18 : deltaMax P ≤ (P.n : ℝ) / ((N : ℝ) * P.chi) * (1 - P.Umax)) :
    IsMonotoneOn (K P) (F P) := by
  intro x hx y hy
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    simp [pair]
  obtain ⟨hU0, hU1, hAl⟩ := hA
  obtain ⟨hn, hchi0, hchi1⟩ := hS
  have hnR : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  -- the weights
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (1 - P.Umax) / N := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact div_pos (by linarith) hNR
  have hNc : (N : ℝ) * c = 1 - P.Umax := by rw [hcdef]; field_simp
  have hbound : deltaMax P * ((N : ℝ) * P.chi) ≤ P.n * (1 - P.Umax) := by
    have h1 := mul_le_mul_of_nonneg_right h18 (by positivity : (0 : ℝ) ≤ (N : ℝ) * P.chi)
    have e : (P.n : ℝ) / ((N : ℝ) * P.chi) * (1 - P.Umax) * ((N : ℝ) * P.chi)
        = P.n * (1 - P.Umax) := by field_simp
    linarith
  have hwb : ∀ z : Fin N → Tier → ℝ, z ∈ K P → ∀ u, 0 ≤ P.delta u * z u .clet / (P.n : ℝ) ∧
      P.delta u * z u .clet / (P.n : ℝ) ≤ c := by
    intro z hz u
    obtain ⟨_, _, h3, h4⟩ := offl_mem P z hz u
    obtain ⟨_, _, hd0, hd1⟩ := hAl u
    have hdm : P.delta u ≤ deltaMax P := le_ciSup (Set.finite_range _).bddAbove u
    refine ⟨by positivity, ?_⟩
    rw [hcdef, div_le_div_iff₀ hnR hNR]
    have h5 : P.delta u * z u .clet ≤ deltaMax P * P.chi :=
      mul_le_mul hdm h4 h3 (le_trans hd0.le hdm)
    nlinarith [mul_le_mul_of_nonneg_right h5 hNR.le]
  have hD : ∀ z : Fin N → Tier → ℝ, z ∈ K P → 1 - P.Umax ≤ 1 - load P z := by
    intro z hz
    have := hz.2
    have h : load P z ≤ P.Umax := this
    linarith
  -- abbreviations
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 1 / (1 - load P x) := ⟨_, rfl⟩
  obtain ⟨a', ha'def⟩ : ∃ a' : ℝ, a' = 1 / (1 - load P y) := ⟨_, rfl⟩
  have hDx := hD x hx
  have hDy := hD y hy
  have hDxpos : 0 < 1 - load P x := by linarith
  have hDypos : 0 < 1 - load P y := by linarith
  have ha : 0 < a := by rw [hadef]; positivity
  have ha' : 0 < a' := by rw [ha'def]; positivity
  have h1 : a * (N * c) ≤ 1 := by
    rw [hadef, hNc, one_div, ← div_eq_inv_mul, div_le_one hDxpos]; exact hDx
  have h2 : a' * (N * c) ≤ 1 := by
    rw [ha'def, hNc, one_div, ← div_eq_inv_mul, div_le_one hDypos]; exact hDy
  obtain ⟨wx, hwx⟩ : ∃ w : Fin N → ℝ, ∀ u, w u = P.delta u * x u .clet / (P.n : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨wy, hwy⟩ : ∃ w : Fin N → ℝ, ∀ u, w u = P.delta u * y u .clet / (P.n : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hkey := offl_core hN (fun u => wy u - wx u) (fun u => (wx u + wy u) / 2) a a' c ha ha' hc
    (fun u => by
      have := (hwb x hx u).1; have := (hwb y hy u).1
      rw [hwx, hwy] at *; positivity)
    (fun u => by
      have h3 := (hwb x hx u).2; have h4 := (hwb y hy u).2
      rw [← hwx] at h3; rw [← hwy] at h4; linarith)
    h1 h2
  -- the load difference
  have hSd : ∑ u, (wy u - wx u) = (1 - load P x) - (1 - load P y) := by
    rw [Finset.sum_sub_distrib, offl_load_eq P x, offl_load_eq P y]
    simp only [hwx, hwy]
    ring
  have hasub : a' - a = (∑ u, (wy u - wx u)) * (a * a') := by
    rw [hSd, hadef, ha'def]
    field_simp
  -- per user decomposition
  have hper : ∀ u, ∑ i, (F P y - F P x) u i * (y - x) u i
      = (P.alpha u / (1 - P.alpha u * y u .m) ^ 2 - P.alpha u / (1 - P.alpha u * x u .m) ^ 2)
          * (y u .m - x u .m)
        + P.n * ((wy u - wx u) * (a' - a)
          + (a ^ 2 + a' ^ 2) / 2 * (wy u - wx u) ^ 2
          + (a' ^ 2 - a ^ 2) * ((wy u - wx u) * ((wx u + wy u) / 2))) := by
    intro u
    rw [offl_sum_tier]
    have e := offl_clet_alg (P.delta u) (P.n : ℝ) (1 - load P x) (1 - load P y)
      (x u .clet) (y u .clet) (P.beta u) hnR.ne' hDxpos.ne' hDypos.ne'
    simp only [Pi.sub_apply, F]
    rw [offl_T P x u, offl_T P y u]
    rw [hwx, hwy, hadef, ha'def]
    rw [← e]
    ring
  unfold pair
  rw [Finset.sum_congr rfl (fun u _ => hper u), Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_nonneg (Finset.sum_nonneg fun u _ => ?_) (mul_nonneg hnR.le ?_)
  · obtain ⟨m1, m2, _, _⟩ := offl_mem P x hx u
    obtain ⟨n1, n2, _, _⟩ := offl_mem P y hy u
    obtain ⟨h0, hα1, _, _⟩ := hAl u
    exact offl_mpart (P.alpha u) (x u .m) (y u .m) h0 (by nlinarith) (by nlinarith)
  · have hsq : a' ^ 2 - a ^ 2 = (∑ u, (wy u - wx u)) * (a * a') * (a + a') := by
      rw [show a' ^ 2 - a ^ 2 = (a' - a) * (a + a') by ring, hasub]
    have e : ∑ u, ((wy u - wx u) * (a' - a)
          + (a ^ 2 + a' ^ 2) / 2 * (wy u - wx u) ^ 2
          + (a' ^ 2 - a ^ 2) * ((wy u - wx u) * ((wx u + wy u) / 2)))
        = (∑ u, (wy u - wx u)) * (a' - a) + (a ^ 2 + a' ^ 2) / 2 * ∑ u, (wy u - wx u) ^ 2
          + (a' ^ 2 - a ^ 2) * ∑ u, (wy u - wx u) * ((wx u + wy u) / 2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [e, hsq, hasub]
    nlinarith [hkey]
