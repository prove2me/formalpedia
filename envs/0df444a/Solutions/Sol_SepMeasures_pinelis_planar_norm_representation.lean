-- Prove2me | solution 1 for SepMeasures.pinelis_planar_norm_representation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:41:22.856922+00:00
-- url     : https://prove2.me/submissions/70998e81-92f4-45ad-9fda-58943cda7a81

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory SepMeasures Filter Topology NNReal

namespace AuxPinelis

noncomputable section

def vec (θ : ℝ) : E 2 := !₂[Real.cos θ, Real.sin θ]

def perp (θ : ℝ) : E 2 := !₂[-Real.sin θ, Real.cos θ]

def step (m : ℕ) : ℝ := Real.pi / (2 * (m : ℝ))

lemma vec_add_pi (θ : ℝ) : vec (θ + Real.pi) = -vec θ := by
  ext i
  fin_cases i
  · simp [vec, Real.cos_add_pi]
  · simp [vec, Real.sin_add_pi]

lemma norm_perp (θ : ℝ) : ‖perp θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Fin.isValue, perp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs]
  have h : (-Real.sin θ) ^ 2 + Real.cos θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h, Real.sqrt_one]

lemma perp_mem_sphere (θ : ℝ) : perp θ ∈ Metric.sphere (0 : E 2) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  exact norm_perp θ

lemma inner_perp_vec (α θ : ℝ) : inner ℝ (perp α) (vec θ) = Real.sin (θ - α) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, Fin.isValue,
    star_trivial, perp, vec, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_sub]
  ring

lemma two_cos_smul_vec (t h : ℝ) :
    (2 * Real.cos h) • vec t = vec (t + h) + vec (t - h) := by
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul, PiLp.add_apply, vec,
      Matrix.cons_val_zero, Real.cos_add, Real.cos_sub]
    ring
  · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul, PiLp.add_apply, vec,
      Matrix.cons_val_one, Matrix.cons_val_zero, Real.sin_add, Real.sin_sub]
    ring

lemma g_pi_periodic (N : Seminorm ℝ (E 2)) (θ : ℝ) :
    N (vec (θ + Real.pi)) = N (vec θ) := by
  rw [vec_add_pi, map_neg_eq_map]

lemma g_pi_periodic_sub (N : Seminorm ℝ (E 2)) (θ : ℝ) :
    N (vec (θ - Real.pi)) = N (vec θ) := by
  have h := g_pi_periodic N (θ - Real.pi)
  rw [sub_add_cancel] at h
  exact h.symm

lemma second_diff_nonneg (N : Seminorm ℝ (E 2)) (t : ℝ) {h : ℝ}
    (hh0 : 0 < h) (hhpi : h < Real.pi / 2) :
    0 ≤ N (vec (t + h)) - 2 * Real.cos h * N (vec t) + N (vec (t - h)) := by
  have hcos : 0 < Real.cos h := Real.cos_pos_of_mem_Ioo ⟨by linarith, hhpi⟩
  have h1 : 2 * Real.cos h * N (vec t) = N ((2 * Real.cos h) • vec t) := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : N ((2 * Real.cos h) • vec t) ≤ N (vec (t + h)) + N (vec (t - h)) := by
    rw [two_cos_smul_vec]
    exact map_add_le_add N _ _
  linarith

lemma step_pos {m : ℕ} (hm : 1 ≤ m) : 0 < step m := by
  unfold step
  have hm_r : (1 : ℝ) ≤ m := by exact_mod_cast hm
  positivity

lemma step_lt_pi_div_two {m : ℕ} (hm : 2 ≤ m) : step m < Real.pi / 2 := by
  unfold step
  have hm_r : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_pos]

lemma sin_step_pos {m : ℕ} (hm : 2 ≤ m) : 0 < Real.sin (step m) :=
  Real.sin_pos_of_pos_of_lt_pi (step_pos (by omega))
    ((step_lt_pi_div_two hm).trans (by linarith [Real.pi_pos]))

lemma two_m_mul_step {m : ℕ} (hm : 1 ≤ m) :
    ((2 * m : ℕ) : ℝ) * step m = Real.pi := by
  unfold step
  have hm_r : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  exact mul_div_cancel₀ _ (by positivity)

lemma discrete_green_zero {G : ℝ → ℝ} (hper : ∀ θ, G (θ + Real.pi) = G θ)
    (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (2 * m),
        (G (((k : ℝ) + 1) * step m) - 2 * Real.cos (step m) * G ((k : ℝ) * step m) +
          G (((k : ℝ) - 1) * step m)) * Real.sin ((k : ℝ) * step m) =
      2 * Real.sin (step m) * G 0 := by
  set M := 2 * m
  set h := step m
  have hMh : (M : ℝ) * h = Real.pi := two_m_mul_step hm
  let F (k : ℕ) : ℝ :=
    G ((k : ℝ) * h) * Real.sin (((k : ℝ) - 1) * h) -
      G (((k : ℝ) - 1) * h) * Real.sin ((k : ℝ) * h)
  have hstep : ∀ k : ℕ,
      (G (((k : ℝ) + 1) * h) - 2 * Real.cos h * G ((k : ℝ) * h) + G (((k : ℝ) - 1) * h)) *
        Real.sin ((k : ℝ) * h) = F (k + 1) - F k := by
    intro k
    dsimp [F]
    push_cast
    have h1 : ((k : ℝ) + 1 - 1) * h = (k : ℝ) * h := by ring
    have htrig : Real.sin (((k : ℝ) + 1) * h) + Real.sin (((k : ℝ) - 1) * h) =
        2 * Real.sin ((k : ℝ) * h) * Real.cos h := by
      have e1 : ((k : ℝ) + 1) * h = (k : ℝ) * h + h := by ring
      have e2 : ((k : ℝ) - 1) * h = (k : ℝ) * h - h := by ring
      rw [e1, e2, Real.sin_add, Real.sin_sub]
      ring
    rw [h1]
    linear_combination G ((k : ℝ) * h) * htrig
  simp_rw [hstep]
  rw [Finset.sum_range_sub F M]
  dsimp [F]
  have eM1 : ((M : ℝ) - 1) * h = Real.pi - h := by linear_combination hMh
  have e01 : ((0 : ℕ) : ℝ) * h = 0 := by simp
  have e02 : (((0 : ℕ) : ℝ) - 1) * h = -h := by ring
  rw [hMh, eM1, e01, e02, show G Real.pi = G 0 by simpa using hper 0,
    Real.sin_pi, Real.sin_pi_sub, Real.sin_zero, Real.sin_neg]
  ring

def weight (N : Seminorm ℝ (E 2)) (m k : ℕ) : ℝ :=
  (N (vec (((k : ℝ) + 1) * step m)) - 2 * Real.cos (step m) * N (vec ((k : ℝ) * step m)) +
    N (vec (((k : ℝ) - 1) * step m))) / (2 * Real.sin (step m))

lemma weight_nonneg (N : Seminorm ℝ (E 2)) {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    0 ≤ weight N m k := by
  unfold weight
  have h1 : (k : ℝ) * step m + step m = ((k : ℝ) + 1) * step m := by ring
  have h2 : (k : ℝ) * step m - step m = ((k : ℝ) - 1) * step m := by ring
  have hnum := second_diff_nonneg N ((k : ℝ) * step m) (step_pos (by omega)) (step_lt_pi_div_two hm)
  rw [h1, h2] at hnum
  have hsin := sin_step_pos hm
  exact div_nonneg hnum (by positivity)

lemma approx_eq_on_grid (N : Seminorm ℝ (E 2)) {m : ℕ} (hm : 2 ≤ m) (j : ℕ)
    (hj : j < 2 * m) :
    ∑ k ∈ Finset.range (2 * m),
        weight N m k * |Real.sin ((j : ℝ) * step m - (k : ℝ) * step m)| =
      N (vec ((j : ℝ) * step m)) := by
  set M := 2 * m
  set h := step m
  have hh0 : 0 < h := step_pos (by omega)
  have hsin : 0 < Real.sin h := sin_step_pos hm
  have hM_pos : 0 < M := by omega
  have hMh : (M : ℝ) * h = Real.pi := two_m_mul_step (by omega)
  let G (θ : ℝ) : ℝ := N (vec ((j : ℝ) * h + θ))
  have hG_per : ∀ θ, G (θ + Real.pi) = G θ := fun θ => by
    dsimp [G]; rw [← add_assoc, g_pi_periodic]
  have hgreen := discrete_green_zero hG_per m (by omega)
  let shift (r : ℕ) : ℕ := (j + r) % M
  have hbij : Finset.sum (Finset.range M)
      (fun k => weight N m k * |Real.sin ((j : ℝ) * h - (k : ℝ) * h)|) =
      Finset.sum (Finset.range M)
        (fun r => weight N m (shift r) *
          |Real.sin ((j : ℝ) * h - (shift r : ℝ) * h)|) := by
    refine (Finset.sum_bij (fun r _ => shift r) ?_ ?_ ?_ ?_).symm
    · intro r _
      exact Finset.mem_range.mpr (Nat.mod_lt _ hM_pos)
    · intro r₁ hr₁ r₂ hr₂ heq
      rw [Finset.mem_range] at hr₁ hr₂
      dsimp [shift] at heq
      by_cases c1 : j + r₁ < M <;> by_cases c2 : j + r₂ < M
      · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at heq; omega
      · exfalso
        have l2 : j + r₂ - M < M := by omega
        rw [Nat.mod_eq_of_lt c1, show j + r₂ = (j + r₂ - M) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt l2] at heq
        omega
      · exfalso
        have l1 : j + r₁ - M < M := by omega
        rw [Nat.mod_eq_of_lt c2, show j + r₁ = (j + r₁ - M) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt l1] at heq
        omega
      · have l1 : j + r₁ - M < M := by omega
        have l2 : j + r₂ - M < M := by omega
        rw [show j + r₁ = (j + r₁ - M) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt l1,
          show j + r₂ = (j + r₂ - M) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt l2] at heq
        omega
    · intro k hk
      rw [Finset.mem_range] at hk
      by_cases hjk : j ≤ k
      · refine ⟨k - j, Finset.mem_range.mpr (by omega), ?_⟩
        dsimp [shift]
        rw [show j + (k - j) = k by omega, Nat.mod_eq_of_lt hk]
      · refine ⟨k + M - j, Finset.mem_range.mpr (by omega), ?_⟩
        dsimp [shift]
        rw [show j + (k + M - j) = k + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
    · intros; rfl
  rw [hbij]
  have hterm : ∀ r ∈ Finset.range M,
      weight N m (shift r) * |Real.sin ((j : ℝ) * h - (shift r : ℝ) * h)| =
        ((G (((r : ℝ) + 1) * h) - 2 * Real.cos h * G ((r : ℝ) * h) + G (((r : ℝ) - 1) * h)) *
          Real.sin ((r : ℝ) * h)) / (2 * Real.sin h) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hr_nonneg : 0 ≤ (r : ℝ) * h := by positivity
    have hr_lt_pi : (r : ℝ) * h < Real.pi := by
      have : (r : ℝ) < M := by exact_mod_cast hr
      calc (r : ℝ) * h < (M : ℝ) * h := mul_lt_mul_of_pos_right this hh0
        _ = Real.pi := hMh
    have hsin_r_nn : 0 ≤ Real.sin ((r : ℝ) * h) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hr_nonneg hr_lt_pi.le
    by_cases hc : j + r < M
    · have hsh : shift r = j + r := Nat.mod_eq_of_lt hc
      rw [hsh]
      unfold weight
      change (N (vec ((((j + r : ℕ) : ℝ) + 1) * h)) -
          2 * Real.cos h * N (vec (((j + r : ℕ) : ℝ) * h)) +
          N (vec ((((j + r : ℕ) : ℝ) - 1) * h))) / (2 * Real.sin h) *
          |Real.sin ((j : ℝ) * h - ((j + r : ℕ) : ℝ) * h)| = _
      push_cast
      have harg : (j : ℝ) * h - ((j : ℝ) + (r : ℝ)) * h = -((r : ℝ) * h) := by ring
      have habs : |Real.sin ((j : ℝ) * h - ((j : ℝ) + (r : ℝ)) * h)| = Real.sin ((r : ℝ) * h) := by
        rw [harg, Real.sin_neg, abs_neg, abs_of_nonneg hsin_r_nn]
      have a1 : ((j : ℝ) + (r : ℝ) + 1) * h = (j : ℝ) * h + ((r : ℝ) + 1) * h := by ring
      have a2 : ((j : ℝ) + (r : ℝ)) * h = (j : ℝ) * h + (r : ℝ) * h := by ring
      have a3 : ((j : ℝ) + (r : ℝ) - 1) * h = (j : ℝ) * h + ((r : ℝ) - 1) * h := by ring
      dsimp only [G]
      rw [habs, a1, a2, a3, div_mul_eq_mul_div]
    · have hl : j + r - M < M := by omega
      have hsh : shift r = j + r - M := by
        conv_lhs => dsimp [shift]; rw [show j + r = (j + r - M) + M by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hl]
      rw [hsh]
      unfold weight
      have hcast : ((j + r - M : ℕ) : ℝ) = (j : ℝ) + (r : ℝ) - (M : ℝ) := by
        have hle : M ≤ j + r := not_lt.mp hc
        rw [Nat.cast_sub hle, Nat.cast_add]
      change (N (vec ((((j + r - M : ℕ) : ℝ) + 1) * h)) -
          2 * Real.cos h * N (vec (((j + r - M : ℕ) : ℝ) * h)) +
          N (vec ((((j + r - M : ℕ) : ℝ) - 1) * h))) / (2 * Real.sin h) *
          |Real.sin ((j : ℝ) * h - ((j + r - M : ℕ) : ℝ) * h)| = _
      rw [hcast]
      have harg : (j : ℝ) * h - ((j : ℝ) + (r : ℝ) - (M : ℝ)) * h = Real.pi - (r : ℝ) * h := by
        linear_combination hMh
      have habs : |Real.sin ((j : ℝ) * h - ((j : ℝ) + (r : ℝ) - (M : ℝ)) * h)| =
          Real.sin ((r : ℝ) * h) := by
        rw [harg, Real.sin_pi_sub, abs_of_nonneg hsin_r_nn]
      have b1 : ((j : ℝ) + (r : ℝ) - (M : ℝ) + 1) * h =
          ((j : ℝ) * h + ((r : ℝ) + 1) * h) - Real.pi := by linear_combination -hMh
      have b2 : ((j : ℝ) + (r : ℝ) - (M : ℝ)) * h =
          ((j : ℝ) * h + (r : ℝ) * h) - Real.pi := by linear_combination -hMh
      have b3 : ((j : ℝ) + (r : ℝ) - (M : ℝ) - 1) * h =
          ((j : ℝ) * h + ((r : ℝ) - 1) * h) - Real.pi := by linear_combination -hMh
      dsimp only [G]
      rw [habs, b1, b2, b3, g_pi_periodic_sub, g_pi_periodic_sub, g_pi_periodic_sub,
        div_mul_eq_mul_div]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  change (∑ k ∈ Finset.range (2 * m), _) / (2 * Real.sin (step m)) = _
  rw [hgreen]
  dsimp [G]
  rw [add_zero]
  have hs_ne : Real.sin (step m) ≠ 0 := (sin_step_pos hm).ne'
  field_simp [hs_ne]

def approxNorm (N : Seminorm ℝ (E 2)) (m : ℕ) (z : E 2) : ℝ :=
  ∑ k ∈ Finset.range (2 * m), weight N m k * |inner ℝ (perp ((k : ℝ) * step m)) z|

lemma sum_weights_le (N : Seminorm ℝ (E 2)) {m : ℕ} (hm : 2 ≤ m) :
    ∑ k ∈ Finset.range (2 * m), weight N m k ≤ N (vec 0) + N (vec (Real.pi / 2)) := by
  set M := 2 * m
  set h := step m
  have hj0 := approx_eq_on_grid N hm 0 (by omega)
  have hjm := approx_eq_on_grid N hm m (by omega)
  have hm_half : (m : ℝ) * h = Real.pi / 2 := by
    dsimp [h, step]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp [hm0]
  rw [Nat.cast_zero, zero_mul] at hj0
  rw [hm_half] at hjm
  have hle : ∀ k ∈ Finset.range M,
      weight N m k ≤
        weight N m k * |Real.sin (0 - (k : ℝ) * h)| +
          weight N m k * |Real.sin (Real.pi / 2 - (k : ℝ) * h)| := by
    intro k _
    have hw := weight_nonneg N hm k
    rw [← mul_add, zero_sub, Real.sin_neg, abs_neg, Real.sin_pi_div_two_sub]
    have htrig : 1 ≤ |Real.sin ((k : ℝ) * h)| + |Real.cos ((k : ℝ) * h)| := by
      have s1 : |Real.sin ((k : ℝ) * h)| ≤ 1 := Real.abs_sin_le_one _
      have c1 : |Real.cos ((k : ℝ) * h)| ≤ 1 := Real.abs_cos_le_one _
      have sq1 := Real.sin_sq_add_cos_sq ((k : ℝ) * h)
      have hsq_abs : |Real.sin ((k : ℝ) * h)| ^ 2 + |Real.cos ((k : ℝ) * h)| ^ 2 = 1 := by
        rwa [sq_abs, sq_abs]
      nlinarith [abs_nonneg (Real.sin ((k : ℝ) * h)), abs_nonneg (Real.cos ((k : ℝ) * h))]
    exact le_mul_of_one_le_right hw htrig
  calc ∑ k ∈ Finset.range M, weight N m k
    _ ≤ ∑ k ∈ Finset.range M,
          (weight N m k * |Real.sin (0 - (k : ℝ) * h)| +
            weight N m k * |Real.sin (Real.pi / 2 - (k : ℝ) * h)|) := Finset.sum_le_sum hle
    _ = (∑ k ∈ Finset.range M, weight N m k * |Real.sin (0 - (k : ℝ) * h)|) +
          ∑ k ∈ Finset.range M, weight N m k * |Real.sin (Real.pi / 2 - (k : ℝ) * h)| :=
        Finset.sum_add_distrib
    _ = N (vec 0) + N (vec (Real.pi / 2)) := by rw [hj0, hjm]

lemma polar_E2 (z : E 2) :
    ∃ (s : ℝ) (θ : ℝ), |s| = ‖z‖ ∧ θ ∈ Set.Ico 0 Real.pi ∧ z = s • vec θ := by
  by_cases hz : z = 0
  · refine ⟨0, 0, by simp [hz], ⟨le_rfl, Real.pi_pos⟩, ?_⟩
    simp [hz]
  · have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let u : E 2 := ‖z‖⁻¹ • z
    have hu_sq : u 0 ^ 2 + u 1 ^ 2 = 1 := by
      have hu_norm : ‖u‖ = 1 := by
        dsimp [u]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos),
          inv_mul_cancel₀ hnorm_pos.ne']
      have hsq : ‖u‖ ^ 2 = 1 := by rw [hu_norm, one_pow]
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)] at hsq
      simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using hsq
    have half_unit : ∀ v : E 2, v 0 ^ 2 + v 1 ^ 2 = 1 → 0 ≤ v 1 → ¬ (v 1 = 0 ∧ v 0 < 0) →
        ∃ θ ∈ Set.Ico 0 Real.pi, v = vec θ := by
      intro v hv_sq hv1 hnot
      have hv0_mem : v 0 ∈ Set.Icc (-1 : ℝ) 1 := by
        rw [Set.mem_Icc]; constructor <;> nlinarith [sq_nonneg (v 1)]
      refine ⟨Real.arccos (v 0), ⟨Real.arccos_nonneg _, ?_⟩, ?_⟩
      · refine lt_of_le_of_ne (Real.arccos_le_pi _) fun hpi => ?_
        have hcos := congrArg Real.cos hpi
        rw [Real.cos_arccos hv0_mem.1 hv0_mem.2, Real.cos_pi] at hcos
        have hv1_0 : v 1 = 0 := by nlinarith
        exact hnot ⟨hv1_0, by linarith⟩
      · ext i
        fin_cases i
        · simp [vec, Real.cos_arccos hv0_mem.1 hv0_mem.2]
        · simp only [Fin.mk_one, Fin.isValue, vec, Matrix.cons_val_one, Matrix.cons_val_zero,
            Real.sin_arccos]
          have : 1 - v 0 ^ 2 = v 1 ^ 2 := by linarith
          rw [this, Real.sqrt_sq hv1]
    have hz_eq_u : z = ‖z‖ • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hnorm_pos.ne', one_smul]
    by_cases hc : 0 ≤ u 1 ∧ ¬ (u 1 = 0 ∧ u 0 < 0)
    · obtain ⟨θ, hθ, hu_vec⟩ := half_unit u hu_sq hc.1 hc.2
      refine ⟨‖z‖, θ, abs_of_pos hnorm_pos, hθ, ?_⟩
      conv_lhs => rw [hz_eq_u]
      rw [hu_vec]
    · have hneg_sq : (-u) 0 ^ 2 + (-u) 1 ^ 2 = 1 := by simp [hu_sq]
      have hneg_cond : 0 ≤ (-u) 1 ∧ ¬ ((-u) 1 = 0 ∧ (-u) 0 < 0) := by
        simp only [PiLp.neg_apply]
        by_cases hu1 : 0 ≤ u 1
        · have hboth : u 1 = 0 ∧ u 0 < 0 := by tauto
          exact ⟨by linarith [hboth.1], fun ⟨_, h2⟩ => by linarith [hboth.2]⟩
        · exact ⟨by linarith, fun ⟨h1, _⟩ => by linarith⟩
      obtain ⟨θ, hθ, hnegu_vec⟩ := half_unit (-u) hneg_sq hneg_cond.1 hneg_cond.2
      refine ⟨-‖z‖, θ, by rw [abs_neg, abs_of_pos hnorm_pos], hθ, ?_⟩
      have hu_eq : u = -vec θ := by rw [← hnegu_vec, neg_neg]
      conv_lhs => rw [hz_eq_u]
      rw [hu_eq, smul_neg, neg_smul]

lemma norm_vec_sub_le (θ₁ θ₂ : ℝ) : ‖vec θ₁ - vec θ₂‖ ≤ 2 * |θ₁ - θ₂| := by
  have hc : |Real.cos θ₁ - Real.cos θ₂| ≤ |θ₁ - θ₂| := Real.abs_cos_sub_cos_le θ₁ θ₂
  have hs : |Real.sin θ₁ - Real.sin θ₂| ≤ |θ₁ - θ₂| := Real.abs_sin_sub_sin_le θ₁ θ₂
  rw [EuclideanSpace.norm_eq]
  have hsq : ∑ i : Fin 2, ‖(vec θ₁ - vec θ₂) i‖ ^ 2 ≤ (2 * |θ₁ - θ₂|) ^ 2 := by
    simp only [Fin.sum_univ_two, Fin.isValue, PiLp.sub_apply, vec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.norm_eq_abs]
    nlinarith [abs_nonneg (Real.cos θ₁ - Real.cos θ₂), abs_nonneg (Real.sin θ₁ - Real.sin θ₂),
      abs_nonneg (θ₁ - θ₂)]
  exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))

lemma seminorm_lipschitz (N : Seminorm ℝ (E 2)) (x y : E 2) :
    |N x - N y| ≤ (N (vec 0) + N (vec (Real.pi / 2))) * ‖x - y‖ := by
  have hexp : ∀ z : E 2, z = (z 0) • vec 0 + (z 1) • vec (Real.pi / 2) := by
    intro z
    ext i
    fin_cases i <;> simp [vec]
  have hbound : ∀ z : E 2, N z ≤ (N (vec 0) + N (vec (Real.pi / 2))) * ‖z‖ := by
    intro z
    have h0 : |z 0| ≤ ‖z‖ := PiLp.norm_apply_le z 0
    have h1 : |z 1| ≤ ‖z‖ := PiLp.norm_apply_le z 1
    calc N z = N ((z 0) • vec 0 + (z 1) • vec (Real.pi / 2)) := by rw [← hexp z]
      _ ≤ N ((z 0) • vec 0) + N ((z 1) • vec (Real.pi / 2)) := map_add_le_add N _ _
      _ = |z 0| * N (vec 0) + |z 1| * N (vec (Real.pi / 2)) := by
          rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖z‖ * N (vec 0) + ‖z‖ * N (vec (Real.pi / 2)) :=
          add_le_add (mul_le_mul_of_nonneg_right h0 (apply_nonneg N _))
            (mul_le_mul_of_nonneg_right h1 (apply_nonneg N _))
      _ = (N (vec 0) + N (vec (Real.pi / 2))) * ‖z‖ := by ring
  rw [abs_sub_le_iff]
  constructor
  · have h := map_add_le_add N (x - y) y
    rw [sub_add_cancel] at h
    linarith [hbound (x - y)]
  · have h := map_add_le_add N (y - x) x
    rw [sub_add_cancel] at h
    have hneg : N (y - x) = N (x - y) := by
      have : y - x = -(x - y) := by abel
      rw [this, map_neg_eq_map]
    linarith [hbound (x - y)]

lemma approxNorm_lipschitz (N : Seminorm ℝ (E 2)) {m : ℕ} (hm : 2 ≤ m) (x y : E 2) :
    |approxNorm N m x - approxNorm N m y| ≤ (N (vec 0) + N (vec (Real.pi / 2))) * ‖x - y‖ := by
  unfold approxNorm
  rw [← Finset.sum_sub_distrib]
  have h1 : |∑ k ∈ Finset.range (2 * m),
      (weight N m k * |inner ℝ (perp ((k : ℝ) * step m)) x| -
        weight N m k * |inner ℝ (perp ((k : ℝ) * step m)) y|)| ≤
      ∑ k ∈ Finset.range (2 * m), weight N m k * ‖x - y‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hw := weight_nonneg N hm k
    rw [← mul_sub, abs_mul, abs_of_nonneg hw]
    refine mul_le_mul_of_nonneg_left ?_ hw
    have ha := abs_abs_sub_abs_le_abs_sub (inner ℝ (perp ((k : ℝ) * step m)) x)
      (inner ℝ (perp ((k : ℝ) * step m)) y)
    rw [← inner_sub_right] at ha
    exact ha.trans ((abs_real_inner_le_norm _ _).trans_eq (by rw [norm_perp, one_mul]))
  calc |∑ k ∈ Finset.range (2 * m),
        (weight N m k * |inner ℝ (perp ((k : ℝ) * step m)) x| -
          weight N m k * |inner ℝ (perp ((k : ℝ) * step m)) y|)|
    _ ≤ (∑ k ∈ Finset.range (2 * m), weight N m k) * ‖x - y‖ := by
        rwa [← Finset.sum_mul] at h1
    _ ≤ (N (vec 0) + N (vec (Real.pi / 2))) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (sum_weights_le N hm) (norm_nonneg _)

lemma tendsto_approxNorm (N : Seminorm ℝ (E 2)) (z : E 2) :
    Tendsto (fun n : ℕ => approxNorm N (n + 2) z) atTop (𝓝 (N z)) := by
  obtain ⟨s, θ, _hs_abs, hθ_Ico, rfl⟩ := polar_E2 z
  let B := N (vec 0) + N (vec (Real.pi / 2))
  have hB_nn : 0 ≤ B := add_nonneg (apply_nonneg N _) (apply_nonneg N _)
  have hbound : ∀ n : ℕ,
      |approxNorm N (n + 2) (s • vec θ) - N (s • vec θ)| ≤
        |s| * (4 * B * step (n + 2)) := by
    intro n
    set m := n + 2
    have hm : 2 ≤ m := by omega
    set M := 2 * m
    set h := step m
    have hh0 : 0 < h := step_pos (by omega)
    have hM_pos : 0 < M := by omega
    have hMh : (M : ℝ) * h = Real.pi := two_m_mul_step (by omega)
    let j : ℕ := min ⌊θ / h⌋₊ (M - 1)
    have hj_lt : j < M := by dsimp [j]; omega
    have hθ_div_lt : θ / h < M := by
      rw [div_lt_iff₀ hh0, hMh]; exact hθ_Ico.2
    have hfloor_lt : ⌊θ / h⌋₊ < M :=
      (Nat.floor_lt (div_nonneg hθ_Ico.1 hh0.le)).mpr hθ_div_lt
    have hj_eq : j = ⌊θ / h⌋₊ := min_eq_left (Nat.le_sub_one_of_lt hfloor_lt)
    have hj_le : (j : ℝ) * h ≤ θ := by
      rw [hj_eq]
      exact (le_div_iff₀ hh0).mp (Nat.floor_le (div_nonneg hθ_Ico.1 hh0.le))
    have hθ_lt : θ < ((j : ℝ) + 1) * h := by
      rw [hj_eq]
      exact (div_lt_iff₀ hh0).mp (Nat.lt_floor_add_one _)
    have hdiff_θ : |θ - (j : ℝ) * h| ≤ h := by
      rw [abs_le]; constructor <;> linarith
    have hgrid_eq : approxNorm N m (vec ((j : ℝ) * h)) = N (vec ((j : ℝ) * h)) := by
      have ha := approx_eq_on_grid N hm j hj_lt
      unfold approxNorm
      simpa [inner_perp_vec, h] using ha
    have hscale_approx : ∀ v : E 2, approxNorm N m (s • v) = |s| * approxNorm N m v := by
      intro v
      unfold approxNorm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [inner_smul_right, abs_mul]
      ring
    have hscale_N : ∀ v : E 2, N (s • v) = |s| * N v := fun v => by
      rw [map_smul_eq_mul, Real.norm_eq_abs]
    rw [hscale_approx, hscale_N, ← mul_sub, abs_mul, abs_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
    have l1 := approxNorm_lipschitz N hm (vec θ) (vec ((j : ℝ) * h))
    have l2 := seminorm_lipschitz N (vec ((j : ℝ) * h)) (vec θ)
    rw [norm_sub_rev] at l2
    have l3 : ‖vec θ - vec ((j : ℝ) * h)‖ ≤ 2 * h :=
      (norm_vec_sub_le _ _).trans (by linarith)
    have hsum_lip : |approxNorm N m (vec θ) - N (vec θ)| ≤ 2 * B * ‖vec θ - vec ((j : ℝ) * h)‖ := by
      have htri : |approxNorm N m (vec θ) - N (vec θ)| ≤
          |approxNorm N m (vec θ) - approxNorm N m (vec ((j : ℝ) * h))| +
            |N (vec ((j : ℝ) * h)) - N (vec θ)| := by
        rw [← hgrid_eq]
        exact abs_sub_le _ _ _
      dsimp [B]
      linarith
    calc |approxNorm N m (vec θ) - N (vec θ)|
      _ ≤ 2 * B * (2 * h) := hsum_lip.trans (mul_le_mul_of_nonneg_left l3 (by positivity))
      _ = 4 * B * h := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (Real.norm_eq_abs _).le.trans (hbound n)) ?_
  have hstep_tend : Tendsto (fun n : ℕ => step (n + 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => (Real.pi / 2) * (1 / (((n + 1 : ℕ) : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using h1.const_mul (Real.pi / 2)
    refine h2.congr fun n => ?_
    dsimp [step]
    push_cast
    field_simp
    ring
  have h0 : |s| * (4 * B * (0 : ℝ)) = 0 := by ring
  rw [← h0]
  exact ((hstep_tend.const_mul (4 * B)).const_mul |s|)

end

end AuxPinelis

theorem solution (N : Seminorm ℝ (E 2)) (hN : ∀ x, N x = 0 → x = 0) :
    ∃ ρ : Measure (E 2), IsFiniteMeasure ρ ∧ ρ {0} = 0 ∧
      ∀ z : E 2, ENNReal.ofReal (N z) = ∫⁻ a, ENNReal.ofReal |inner ℝ a z| ∂ρ := by
  have _ := hN
  let S1 := Metric.sphere (0 : E 2) 1
  have : CompactSpace S1 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E 2) 1)
  let B : ℝ := N (AuxPinelis.vec 0) + N (AuxPinelis.vec (Real.pi / 2))
  have hB_nn : 0 ≤ B := add_nonneg (apply_nonneg N _) (apply_nonneg N _)
  let μS (n : ℕ) : Measure S1 :=
    ∑ k ∈ Finset.range (2 * (n + 2)),
      ENNReal.ofReal (AuxPinelis.weight N (n + 2) k) •
        Measure.dirac ⟨AuxPinelis.perp ((k : ℝ) * AuxPinelis.step (n + 2)),
          AuxPinelis.perp_mem_sphere _⟩
  have hμS_univ : ∀ n : ℕ, μS n Set.univ ≤ ENNReal.ofReal B := by
    intro n
    dsimp [μS]
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
      Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => AuxPinelis.weight_nonneg N (by omega) k)]
    exact ENNReal.ofReal_le_ofReal (AuxPinelis.sum_weights_le N (by omega))
  let FM (n : ℕ) : FiniteMeasure S1 :=
    ⟨μS n, ⟨(hμS_univ n).trans_lt ENNReal.ofReal_lt_top⟩⟩
  let C_nn : ℝ≥0 := Real.toNNReal B
  have hFM_mass : ∀ n : ℕ, (FM n).mass ≤ C_nn := by
    intro n
    change ((μS n) Set.univ).toNNReal ≤ Real.toNNReal B
    have hle := ENNReal.toNNReal_mono ENNReal.ofReal_ne_top (hμS_univ n)
    have hcoe : (ENNReal.ofReal B).toNNReal = Real.toNNReal B :=
      ENNReal.toNNReal_coe (Real.toNNReal B)
    rwa [hcoe] at hle
  have hK : IsCompact {μ : FiniteMeasure S1 | μ.mass ≤ C_nn} :=
    isCompact_setOfPred_finiteMeasure_le_of_compactSpace S1 C_nn
  let uf : Ultrafilter ℕ := Ultrafilter.of atTop
  have huf_le : (uf : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hmem : {μ : FiniteMeasure S1 | μ.mass ≤ C_nn} ∈ uf.map FM :=
    Ultrafilter.mem_map.mpr (Filter.Eventually.of_forall hFM_mass)
  obtain ⟨μ_lim, _, h_tend⟩ := hK.ultrafilter_le_nhds' _ hmem
  let ρ : Measure (E 2) := (μ_lim : Measure S1).map Subtype.val
  refine ⟨ρ, inferInstance, ?_, ?_⟩
  · dsimp [ρ]
    rw [Measure.map_apply continuous_subtype_val.measurable (measurableSet_singleton 0)]
    have hempty : (Subtype.val : S1 → E 2) ⁻¹' {0} = ∅ := by
      ext ⟨a, ha⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro ha0
      have h1 : ‖a‖ = 1 := by simpa [S1] using ha
      rw [ha0, norm_zero] at h1
      norm_num at h1
    rw [hempty, measure_empty]
  · intro z
    let fz_cm : C(S1, ℝ≥0) :=
      ⟨fun a => Real.toNNReal |inner ℝ (a : E 2) z|,
        continuous_real_toNNReal.comp
          (continuous_abs.comp (continuous_subtype_val.inner continuous_const))⟩
    let fz : BoundedContinuousFunction S1 ℝ≥0 := BoundedContinuousFunction.mkOfCompact fz_cm
    have htend_lint :=
      (FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp h_tend) fz
    have hfz_eq : ∀ a : S1, (fz a : ENNReal) = ENNReal.ofReal |inner ℝ (a : E 2) z| := by
      intro a
      rfl
    have hdiscrete : ∀ n : ℕ,
        (∫⁻ a : S1, (fz a : ENNReal) ∂(FM n : Measure S1)) =
          ENNReal.ofReal (AuxPinelis.approxNorm N (n + 2) z) := by
      intro n
      change (∫⁻ a : S1, (fz a : ENNReal) ∂(μS n)) = _
      dsimp [μS]
      rw [lintegral_finsetSum_measure]
      have hterm : ∀ k ∈ Finset.range (2 * (n + 2)),
          (∫⁻ a : S1, (fz a : ENNReal) ∂(ENNReal.ofReal (AuxPinelis.weight N (n + 2) k) •
              Measure.dirac ⟨AuxPinelis.perp ((k : ℝ) * AuxPinelis.step (n + 2)),
                AuxPinelis.perp_mem_sphere _⟩)) =
            ENNReal.ofReal (AuxPinelis.weight N (n + 2) k *
              |inner ℝ (AuxPinelis.perp ((k : ℝ) * AuxPinelis.step (n + 2))) z|) := by
        intro k _
        rw [lintegral_smul_measure, lintegral_dirac, hfz_eq]
        exact (ENNReal.ofReal_mul (AuxPinelis.weight_nonneg N (by omega) k)).symm
      rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg
        (fun k _ => mul_nonneg (AuxPinelis.weight_nonneg N (by omega) k) (abs_nonneg _))]
      rfl
    simp_rw [hdiscrete] at htend_lint
    have htend_N : Tendsto (fun n : ℕ => ENNReal.ofReal (AuxPinelis.approxNorm N (n + 2) z))
        (uf : Filter ℕ) (𝓝 (ENNReal.ofReal (N z))) :=
      (ENNReal.continuous_ofReal.tendsto (N z)).comp
        ((AuxPinelis.tendsto_approxNorm N z).mono_left huf_le)
    have heq_lim : ENNReal.ofReal (N z) =
        ∫⁻ a : S1, (fz a : ENNReal) ∂(μ_lim : Measure S1) :=
      tendsto_nhds_unique htend_N htend_lint
    rw [heq_lim]
    simp_rw [hfz_eq]
    dsimp [ρ]
    have hm_integrand : Measurable (fun a : E 2 => ENNReal.ofReal |inner ℝ a z|) :=
      ENNReal.measurable_ofReal.comp (continuous_abs.comp (continuous_id.inner continuous_const)).measurable
    exact (lintegral_map hm_integrand continuous_subtype_val.measurable).symm
