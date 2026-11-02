-- Prove2me | solution 1 for SpikedWishart.FixedDim.proposition_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T04:00:58.226198+00:00
-- url     : https://prove2.me/submissions/e15ff495-b8d6-4152-b68f-f9bab6266784

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_Model
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre
import Theorems.Thm_SpikedWishart_FixedDim_eq_304

set_option autoImplicit false

open MeasureTheory Filter Topology Set

namespace SWFDAux

/-- per-coordinate Laguerre factor after the change of variables of (304). -/
noncomputable def phi (k M : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-Real.sqrt M * t) * (1 + t / Real.sqrt M) ^ (M - k)

lemma phi_bound (k M : ℕ) (hM1 : 1 ≤ M) (hkM : 2 * k ≤ M) (t : ℝ) (ht : -Real.sqrt M ≤ t) :
    0 ≤ phi k M t ∧ phi k M t ≤ Real.exp (k + 1 / 2) * Real.exp (-|t| / 4) := by
  unfold phi
  set s := Real.sqrt M with hs_def
  have hs1 : 1 ≤ s := by
    rw [hs_def]; exact Real.one_le_sqrt.mpr (by exact_mod_cast hM1)
  have hs0 : 0 < s := by linarith
  have hss : s * s = (M : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
  set u := t / s with hu_def
  have hut : s * u = t := by rw [hu_def]; field_simp
  have hu1 : -1 ≤ u := by rw [hu_def, le_div_iff₀ hs0]; linarith
  have h1u : 0 ≤ 1 + u := by linarith
  set n : ℕ := M - k with hn_def
  have hnR : (n : ℝ) = M - k := by rw [hn_def, Nat.cast_sub (by omega)]
  have hkM' : (2 * k : ℝ) ≤ M := by exact_mod_cast hkM
  have hn2 : (M : ℝ) ≤ 2 * n := by rw [hnR]; linarith
  set w := Real.sqrt (1 + u) with hw_def
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hww : w * w = 1 + u := Real.mul_self_sqrt h1u
  have hwexp : w ≤ Real.exp (w - 1) := by have := Real.add_one_le_exp (w - 1); linarith
  have h1 : 1 + u ≤ Real.exp (2 * (w - 1)) := by
    rw [← hww, show 2 * (w - 1) = (w - 1) + (w - 1) by ring, Real.exp_add]
    exact mul_le_mul hwexp hwexp hw0 (Real.exp_pos _).le
  have h2 : (1 + u) ^ n ≤ Real.exp (n * (2 * (w - 1))) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ h1u h1 n
  refine ⟨mul_nonneg (Real.exp_pos _).le (pow_nonneg h1u _), ?_⟩
  have key : -s * t + n * (2 * (w - 1)) = -((n : ℝ) * (w - 1) ^ 2) - k * u := by
    rw [← hut]; linear_combination (n : ℝ) * hww - u * hss + u * hnR
  -- lower bound on n (w-1)^2
  set a := s * (w - 1) with ha_def
  have ha : a * (w + 1) = t := by
    rw [ha_def, ← hut]; linear_combination s * hww
  have habs_u : |u| ≤ |t| := by
    rw [hu_def, abs_div, abs_of_pos hs0]; exact div_le_self (abs_nonneg _) hs1
  have hw1 : (w + 1) ^ 2 ≤ 2 * (2 + |t|) := by
    have : u ≤ |t| := (le_abs_self u).trans habs_u
    nlinarith [sq_nonneg (w - 1)]
  have hpos : 0 < 2 + |t| := by positivity
  have hA : |t| - 2 ≤ 2 * a ^ 2 := by
    have ht2 : t ^ 2 = a ^ 2 * (w + 1) ^ 2 := by rw [← ha]; ring
    have h3 : (|t| - 2) * (2 + |t|) ≤ 2 * a ^ 2 * (2 + |t|) := by
      have : |t| ^ 2 = t ^ 2 := sq_abs t
      nlinarith [sq_nonneg a, mul_le_mul_of_nonneg_left hw1 (sq_nonneg a)]
    exact le_of_mul_le_mul_right h3 hpos
  have ha2 : a ^ 2 = (M : ℝ) * (w - 1) ^ 2 := by rw [ha_def, ← hss]; ring
  have hn3 : (|t| - 2) / 4 ≤ (n : ℝ) * (w - 1) ^ 2 := by
    have : (M : ℝ) * (w - 1) ^ 2 ≤ 2 * n * (w - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hn2 (sq_nonneg _)
    nlinarith
  have hku : -(k : ℝ) * u ≤ k := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith
  calc Real.exp (-s * t) * (1 + u) ^ n
      ≤ Real.exp (-s * t) * Real.exp (n * (2 * (w - 1))) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-s * t + n * (2 * (w - 1))) := by rw [Real.exp_add]
    _ ≤ Real.exp (k + 1 / 2) * Real.exp (-|t| / 4) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; rw [key]; linarith

lemma expo_u (k : ℝ) (hk : 0 ≤ k) (s u n : ℝ) (hs : 1 ≤ s) (hn : n = s ^ 2 - k) (hn0 : 0 ≤ n)
    (hu : |u| ≤ 1 / 2) :
    |(-s * (s * u) + n * Real.log (1 + u)) + (s * u) ^ 2 / 2| ≤
      2 * s ^ 2 * |u| ^ 3 + k * |u| + k * s * u ^ 2 := by
  have hu1 : |-u| < 1 := by rw [abs_neg]; linarith
  have hR0 := Real.abs_log_sub_add_sum_range_le hu1 2
  have hR : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 2 * |u| ^ 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at hR0
    have e : Real.log (1 + u) - u + u ^ 2 / 2 =
        0 + (-u) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-u) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
          Real.log (1 + u) := by push_cast; ring
    rw [e]
    refine hR0.trans ?_
    have h12 : (1 : ℝ) / 2 ≤ 1 - |u| := by linarith
    rw [div_le_iff₀ (by linarith), show (2 : ℕ) + 1 = 3 from rfl]
    nlinarith [pow_nonneg (abs_nonneg u) 3, mul_le_mul_of_nonneg_left h12 (pow_nonneg (abs_nonneg u) 3)]
  have id : (-s * (s * u) + n * Real.log (1 + u)) + (s * u) ^ 2 / 2 =
      n * (Real.log (1 + u) - u + u ^ 2 / 2) + (-k * u + k * u ^ 2 / 2) := by
    rw [hn]; ring
  rw [id]
  have hn' : n ≤ s ^ 2 := by rw [hn]; linarith
  have e1 : |n * (Real.log (1 + u) - u + u ^ 2 / 2)| ≤ s ^ 2 * (2 * |u| ^ 3) := by
    rw [abs_mul, abs_of_nonneg hn0]
    exact mul_le_mul hn' hR (abs_nonneg _) (by positivity)
  have e2 : |-k * u + k * u ^ 2 / 2| ≤ k * |u| + k * s * u ^ 2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_neg, abs_of_nonneg hk, abs_of_nonneg (by positivity : 0 ≤ k * u ^ 2 / 2)]
    have : k * u ^ 2 / 2 ≤ k * s * u ^ 2 := by nlinarith [sq_nonneg u, mul_nonneg hk (sq_nonneg u)]
    linarith
  calc _ ≤ |n * (Real.log (1 + u) - u + u ^ 2 / 2)| + |-k * u + k * u ^ 2 / 2| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma tendsto_sqrt_nat : Tendsto (fun M : ℕ => Real.sqrt M) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

lemma phi_tendsto (k : ℕ) (t : ℝ) :
    Tendsto (fun M : ℕ => phi k M t) atTop (𝓝 (Real.exp (-t ^ 2 / 2))) := by
  have hinv : Tendsto (fun M : ℕ => (Real.sqrt M)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_sqrt_nat
  -- exponent
  set E : ℕ → ℝ := fun M => -Real.sqrt M * t + ((M - k : ℕ) : ℝ) * Real.log (1 + t / Real.sqrt M)
  have hev1 : ∀ᶠ M : ℕ in atTop, max 1 (2 * |t| + 1) ≤ Real.sqrt M ∧ k ≤ M :=
    (tendsto_sqrt_nat.eventually_ge_atTop _).and (eventually_ge_atTop k)
  have hE : Tendsto E atTop (𝓝 (-t ^ 2 / 2)) := by
    have hb : Tendsto (fun M : ℕ => (2 * |t| ^ 3 + k * |t| + k * t ^ 2) * (Real.sqrt M)⁻¹)
        atTop (𝓝 0) := by simpa using hinv.const_mul (2 * |t| ^ 3 + k * |t| + k * t ^ 2)
    have : Tendsto (fun M => E M - (-t ^ 2 / 2)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [hev1] with M ⟨hM, hkM⟩
      set s := Real.sqrt M with hs_def
      have hs1 : 1 ≤ s := (le_max_left _ _).trans hM
      have hs0 : 0 < s := by linarith
      have hss : s ^ 2 = (M : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
      set u := t / s with hu_def
      have hut : s * u = t := by rw [hu_def]; field_simp
      have hu : |u| ≤ 1 / 2 := by
        rw [hu_def, abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
        have := (le_max_right _ _).trans hM
        linarith
      have hn : (((M - k : ℕ) : ℝ)) = s ^ 2 - k := by rw [Nat.cast_sub hkM, hss]
      have h := expo_u k (Nat.cast_nonneg _) s u _ hs1 hn (Nat.cast_nonneg _) hu
      rw [hut] at h
      have hE' : E M - (-t ^ 2 / 2) = (-s * t + ((M - k : ℕ) : ℝ) * Real.log (1 + u)) + t ^ 2 / 2 := by
        simp only [E]; ring
      rw [Real.norm_eq_abs, hE']
      refine h.trans (le_of_eq ?_)
      rw [← hut]; field_simp
      rw [abs_mul, abs_of_pos hs0]; ring
    have h' := this.add_const (-t ^ 2 / 2)
    simp only [sub_add_cancel, zero_add] at h'
    exact h'
  have hlim := (Real.continuous_exp.tendsto _).comp hE
  refine hlim.congr' ?_
  filter_upwards [hev1] with M ⟨hM, hkM⟩
  have hs0 : 0 < Real.sqrt M := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hM)
  have hpos : 0 < 1 + t / Real.sqrt M := by
    have h2 := (le_max_right _ _).trans hM
    have : |t / Real.sqrt M| < 1 := by
      rw [abs_div, abs_of_pos hs0, div_lt_one hs0]; linarith [abs_nonneg t]
    linarith [neg_abs_le (t / Real.sqrt M)]
  simp only [Function.comp, E, phi]
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hpos]

/-- `(1+t²)^(m+1) ≤ C e^{|t|/4}`. -/
lemma poly_le_exp (m : ℕ) (t : ℝ) :
    (1 + t ^ 2) ^ (m + 1) ≤
      4 ^ (2 * (m + 1)) * ((2 * (m + 1)).factorial : ℝ) * Real.exp (1 / 4) * Real.exp (|t| / 4) := by
  have h1 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have h2 : (1 + t ^ 2) ^ (m + 1) ≤ (1 + |t|) ^ (2 * (m + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) h1 _
  set x := (1 + |t|) / 4 with hx
  have hx0 : 0 ≤ x := by positivity
  have h3 := Real.pow_div_factorial_le_exp x hx0 (2 * (m + 1))
  have hfac : (0 : ℝ) < ((2 * (m + 1)).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hfac] at h3
  have h4 : (1 + |t|) ^ (2 * (m + 1)) = 4 ^ (2 * (m + 1)) * x ^ (2 * (m + 1)) := by
    rw [hx, div_pow, mul_div_cancel₀ _ (by positivity)]
  have h5 : Real.exp x = Real.exp (1 / 4) * Real.exp (|t| / 4) := by
    rw [← Real.exp_add, hx]; ring_nf
  calc (1 + t ^ 2) ^ (m + 1) ≤ (1 + |t|) ^ (2 * (m + 1)) := h2
    _ = 4 ^ (2 * (m + 1)) * x ^ (2 * (m + 1)) := h4
    _ ≤ 4 ^ (2 * (m + 1)) * (Real.exp x * ((2 * (m + 1)).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by rw [h5]; ring

lemma vandSq_nonneg {k : ℕ} (ξ : Fin k → ℝ) : 0 ≤ SpikedWishart.FixedDim.vandSq ξ := by
  unfold SpikedWishart.FixedDim.vandSq
  refine Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => ?_
  split_ifs <;> positivity

lemma vandSq_le {k : ℕ} (ξ : Fin k → ℝ) :
    SpikedWishart.FixedDim.vandSq ξ ≤ 2 ^ (k * k) * ∏ j, (1 + ξ j ^ 2) ^ (2 * k) := by
  unfold SpikedWishart.FixedDim.vandSq
  calc (∏ i, ∏ j, if i < j then (ξ i - ξ j) ^ 2 else 1)
      ≤ ∏ i : Fin k, ∏ j : Fin k, (2 * (1 + ξ i ^ 2) * (1 + ξ j ^ 2)) := by
        refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) fun i _ => ?_
        · split_ifs <;> positivity
        refine Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
        · split_ifs <;> positivity
        split_ifs
        · nlinarith [sq_nonneg (ξ i + ξ j), sq_nonneg (ξ i * ξ j), sq_nonneg (ξ i), sq_nonneg (ξ j)]
        · nlinarith [sq_nonneg (ξ i * ξ j), sq_nonneg (ξ i), sq_nonneg (ξ j)]
    _ = 2 ^ (k * k) * ∏ j, (1 + ξ j ^ 2) ^ (2 * k) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow]
        ring

lemma vandSq_cont (k : ℕ) : Continuous (fun ξ : Fin k → ℝ => SpikedWishart.FixedDim.vandSq ξ) := by
  unfold SpikedWishart.FixedDim.vandSq
  refine continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => ?_
  split_ifs
  · exact ((continuous_apply i).sub (continuous_apply j)).pow 2
  · exact continuous_const

lemma phi_cont (k M : ℕ) : Continuous (phi k M) := by
  unfold phi; fun_prop

noncomputable def psi (k M : ℕ) (ξ : Fin k → ℝ) : ℝ :=
  SpikedWishart.FixedDim.vandSq ξ * ∏ j, (Ici (-Real.sqrt M)).indicator (phi k M) (ξ j)

noncomputable def gfun (k : ℕ) (ξ : Fin k → ℝ) : ℝ :=
  SpikedWishart.FixedDim.vandSq ξ * ∏ i, Real.exp (-(ξ i) ^ 2 / 2)

noncomputable def Cb (k : ℕ) : ℝ :=
  4 ^ (2 * (2 * k + 1)) * ((2 * (2 * k + 1)).factorial : ℝ) * Real.exp (1 / 4)

noncomputable def bet (k : ℕ) (t : ℝ) : ℝ := Real.exp (k + 1 / 2) * Cb k * (1 + t ^ 2)⁻¹

noncomputable def dom (k : ℕ) (ξ : Fin k → ℝ) : ℝ := 2 ^ (k * k) * ∏ j, bet k (ξ j)

lemma bet_bound (k : ℕ) (f : ℝ → ℝ) (h0 : ∀ t, 0 ≤ f t)
    (h1 : ∀ t, f t ≤ Real.exp (k + 1 / 2) * Real.exp (-|t| / 4)) (t : ℝ) :
    (1 + t ^ 2) ^ (2 * k) * f t ≤ bet k t := by
  unfold bet
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hP := poly_le_exp (2 * k) t
  rw [le_mul_inv_iff₀ hp]
  have e1 : (1 + t ^ 2) ^ (2 * k) * f t * (1 + t ^ 2) = (1 + t ^ 2) ^ (2 * k + 1) * f t := by
    rw [pow_succ]; ring
  rw [e1]
  have hE : Real.exp (-|t| / 4) * Real.exp (|t| / 4) = 1 := by
    rw [← Real.exp_add, show -|t| / 4 + |t| / 4 = 0 by ring, Real.exp_zero]
  calc (1 + t ^ 2) ^ (2 * k + 1) * f t
      ≤ (Cb k * Real.exp (|t| / 4)) * (Real.exp (k + 1 / 2) * Real.exp (-|t| / 4)) := by
        refine mul_le_mul ?_ (h1 t) (h0 t) (by unfold Cb; positivity)
        unfold Cb; exact hP
    _ = Real.exp (k + 1 / 2) * Cb k * (Real.exp (-|t| / 4) * Real.exp (|t| / 4)) := by ring
    _ = Real.exp (k + 1 / 2) * Cb k := by rw [hE, mul_one]

lemma main_bound (k : ℕ) (f : ℝ → ℝ) (h0 : ∀ t, 0 ≤ f t)
    (h1 : ∀ t, f t ≤ Real.exp (k + 1 / 2) * Real.exp (-|t| / 4)) (ξ : Fin k → ℝ) :
    0 ≤ SpikedWishart.FixedDim.vandSq ξ * ∏ j, f (ξ j) ∧
      SpikedWishart.FixedDim.vandSq ξ * ∏ j, f (ξ j) ≤ dom k ξ := by
  have hprod : 0 ≤ ∏ j, f (ξ j) := Finset.prod_nonneg fun j _ => h0 _
  refine ⟨mul_nonneg (vandSq_nonneg ξ) hprod, ?_⟩
  calc SpikedWishart.FixedDim.vandSq ξ * ∏ j, f (ξ j)
      ≤ (2 ^ (k * k) * ∏ j, (1 + ξ j ^ 2) ^ (2 * k)) * ∏ j, f (ξ j) :=
        mul_le_mul_of_nonneg_right (vandSq_le ξ) hprod
    _ = 2 ^ (k * k) * ∏ j, ((1 + ξ j ^ 2) ^ (2 * k) * f (ξ j)) := by
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ dom k ξ := by
        unfold dom
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_)
          (by positivity)
        · exact mul_nonneg (by positivity) (h0 _)
        · exact bet_bound k f h0 h1 _

lemma ind_phi_bounds (k M : ℕ) (hM1 : 1 ≤ M) (hkM : 2 * k ≤ M) (t : ℝ) :
    0 ≤ (Ici (-Real.sqrt M)).indicator (phi k M) t ∧
      (Ici (-Real.sqrt M)).indicator (phi k M) t ≤ Real.exp (k + 1 / 2) * Real.exp (-|t| / 4) := by
  by_cases ht : t ∈ Ici (-Real.sqrt M)
  · rw [indicator_of_mem ht]; exact phi_bound k M hM1 hkM t ht
  · rw [indicator_of_notMem ht]; exact ⟨le_rfl, by positivity⟩

lemma gauss_bounds (k : ℕ) (t : ℝ) :
    0 ≤ Real.exp (-t ^ 2 / 2) ∧ Real.exp (-t ^ 2 / 2) ≤ Real.exp (k + 1 / 2) * Real.exp (-|t| / 4) := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith [sq_abs t, sq_nonneg (|t| - 1 / 4)]

lemma bet_integrable (k : ℕ) : Integrable (bet k) := by
  unfold bet
  exact integrable_inv_one_add_sq.const_mul _

lemma dom_integrable (k : ℕ) : Integrable (dom k) := by
  unfold dom
  refine Integrable.const_mul ?_ _
  exact Integrable.fintype_prod (f := fun _ => bet k) (μ := fun _ => volume) fun _ => bet_integrable k

lemma psi_meas (k M : ℕ) : Measurable (psi k M) := by
  unfold psi
  exact (vandSq_cont k).measurable.mul (Finset.measurable_prod _ fun j _ =>
    ((phi_cont k M).measurable.indicator measurableSet_Ici).comp (measurable_pi_apply j))

lemma gfun_meas (k : ℕ) : Measurable (gfun k) := by
  unfold gfun
  exact (vandSq_cont k).measurable.mul (Finset.measurable_prod _ fun j _ =>
    (by fun_prop : Measurable fun t : ℝ => Real.exp (-t ^ 2 / 2)).comp (measurable_pi_apply j))

lemma psi_lim (k : ℕ) (ξ : Fin k → ℝ) :
    Tendsto (fun M : ℕ => psi k M ξ) atTop (𝓝 (gfun k ξ)) := by
  unfold psi gfun
  refine Tendsto.const_mul _ (tendsto_finsetProd _ fun j _ => ?_)
  refine (phi_tendsto k (ξ j)).congr' ?_
  filter_upwards [tendsto_sqrt_nat.eventually_ge_atTop (-ξ j)] with M hM
  rw [indicator_of_mem (show ξ j ∈ Ici (-Real.sqrt M) by simp only [mem_Ici]; linarith)]

lemma psi_tendsto (k : ℕ) (S : Set (Fin k → ℝ)) :
    Tendsto (fun M : ℕ => ∫ ξ in S, psi k M ξ) atTop (𝓝 (∫ ξ in S, gfun k ξ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (dom k)
    (Eventually.of_forall fun M => (psi_meas k M).aestronglyMeasurable) ?_
    (dom_integrable k).integrableOn (ae_of_all _ fun ξ => psi_lim k ξ)
  filter_upwards [eventually_ge_atTop (max 1 (2 * k))] with M hM
  refine ae_of_all _ fun ξ => ?_
  have hb := main_bound k _ (fun t => (ind_phi_bounds k M (le_of_max_le_left hM)
    (le_of_max_le_right hM) t).1) (fun t => (ind_phi_bounds k M (le_of_max_le_left hM)
    (le_of_max_le_right hM) t).2) ξ
  unfold psi
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma gfun_bounds (k : ℕ) (ξ : Fin k → ℝ) : 0 ≤ gfun k ξ ∧ gfun k ξ ≤ dom k ξ :=
  main_bound k _ (fun t => (gauss_bounds k t).1) (fun t => (gauss_bounds k t).2) ξ

lemma gfun_integrable (k : ℕ) : Integrable (gfun k) :=
  (dom_integrable k).mono' (gfun_meas k).aestronglyMeasurable
    (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs, abs_of_nonneg (gfun_bounds k ξ).1]; exact (gfun_bounds k ξ).2)

lemma psi_integrable (k M : ℕ) (hM : max 1 (2 * k) ≤ M) : Integrable (psi k M) := by
  refine (dom_integrable k).mono' (psi_meas k M).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  have hb := main_bound k _ (fun t => (ind_phi_bounds k M (le_of_max_le_left hM)
    (le_of_max_le_right hM) t).1) (fun t => (ind_phi_bounds k M (le_of_max_le_left hM)
    (le_of_max_le_right hM) t).2) ξ
  unfold psi
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma Z_eq (k : ℕ) : SpikedWishart.FixedDim.Z k = ∫ ξ, gfun k ξ := rfl

lemma G_eq (k : ℕ) (x : ℝ) :
    SpikedWishart.FixedDim.G k x =
      (SpikedWishart.FixedDim.Z k)⁻¹ * ∫ ξ in Set.pi univ (fun _ : Fin k => Iic x), gfun k ξ := rfl

lemma Z_pos (k : ℕ) : 0 < SpikedWishart.FixedDim.Z k := by
  rw [Z_eq, integral_pos_iff_support_of_nonneg (fun ξ => (gfun_bounds k ξ).1) (gfun_integrable k)]
  set U : Set (Fin k → ℝ) := ⋂ i : Fin k, ⋂ j : Fin k, {ξ | i < j → ξ i ≠ ξ j} with hU
  have hUo : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    by_cases h : i < j
    · simp only [h, true_implies]
      exact isOpen_ne_fun (continuous_apply i) (continuous_apply j)
    · simp only [h, false_implies, setOf_true, isOpen_univ]
  have hUne : (U).Nonempty := by
    refine ⟨fun i => (i : ℝ), ?_⟩
    simp only [hU, mem_iInter, mem_setOf_eq]
    intro i j hij
    exact_mod_cast (Fin.val_ne_of_ne (ne_of_lt hij))
  have hsub : U ⊆ Function.support (gfun k) := by
    intro ξ hξ
    simp only [hU, mem_iInter, mem_setOf_eq] at hξ
    simp only [Function.mem_support, gfun, SpikedWishart.FixedDim.vandSq]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr
      fun j _ => ?_) (Finset.prod_ne_zero_iff.mpr fun i _ => (Real.exp_pos _).ne')
    split_ifs with h
    · exact pow_ne_zero _ (sub_ne_zero.mpr (hξ i j h))
    · exact one_ne_zero
  exact (hUo.measure_pos volume hUne).trans_le (measure_mono hsub)

lemma iUnion_pi_Iic (k : ℕ) : (⋃ n : ℕ, Set.pi univ (fun _ : Fin k => Iic (n : ℝ))) = univ := by
  refine eq_univ_of_forall fun ξ => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (∑ j, |ξ j|)
  refine ⟨n, fun j _ => ?_⟩
  simp only [mem_Iic]
  calc ξ j ≤ |ξ j| := le_abs_self _
    _ ≤ ∑ j, |ξ j| := Finset.single_le_sum (fun j _ => abs_nonneg (ξ j)) (Finset.mem_univ j)
    _ ≤ n := hn

lemma pi_Iic_mono (k : ℕ) : Monotone (fun n : ℕ => Set.pi univ (fun _ : Fin k => Iic (n : ℝ))) :=
  fun a b hab => Set.pi_mono fun _ _ => Iic_subset_Iic.mpr (by exact_mod_cast hab)

lemma G_top (k : ℕ) : Tendsto (fun n : ℕ => SpikedWishart.FixedDim.G k n) atTop (𝓝 1) := by
  simp only [G_eq]
  have h := tendsto_setIntegral_of_monotone (μ := volume) (f := gfun k)
    (fun n => MeasurableSet.univ_pi fun _ => measurableSet_Iic) (pi_Iic_mono k)
    (gfun_integrable k).integrableOn
  rw [iUnion_pi_Iic, setIntegral_univ, ← Z_eq] at h
  have h2 := h.const_mul (SpikedWishart.FixedDim.Z k)⁻¹
  rwa [inv_mul_cancel₀ (Z_pos k).ne'] at h2

lemma G_bot (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => SpikedWishart.FixedDim.G k (-n)) atTop (𝓝 0) := by
  simp only [G_eq]
  have hanti : Antitone (fun n : ℕ => Set.pi univ (fun _ : Fin k => Iic (-(n : ℝ)))) :=
    fun a b hab => Set.pi_mono fun _ _ => Iic_subset_Iic.mpr (by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith)
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := gfun k)
    (fun n => MeasurableSet.univ_pi fun _ => measurableSet_Iic) hanti
    ⟨0, (gfun_integrable k).integrableOn⟩
  have hempty : (⋂ n : ℕ, Set.pi univ (fun _ : Fin k => Iic (-(n : ℝ)))) = ∅ := by
    refine eq_empty_of_forall_notMem fun ξ hξ => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (-ξ ⟨0, hk⟩)
    have := (mem_iInter.1 hξ n) ⟨0, hk⟩ (mem_univ _)
    simp only [mem_Iic] at this
    linarith
  rw [hempty, Measure.restrict_empty, integral_zero_measure] at h
  have h2 := h.const_mul (SpikedWishart.FixedDim.Z k)⁻¹
  rwa [mul_zero] at h2

open Matrix in
/-- Rayleigh characterisation of an upper bound on all eigenvalues. -/
lemma eig_le_iff {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (hA : A.IsHermitian) (t : ℝ) :
    (∀ i, hA.eigenvalues i ≤ t) ↔
      ∀ x : Fin k → ℂ, (star x ⬝ᵥ (A *ᵥ x)).re ≤ t * (star x ⬝ᵥ x).re := by
  constructor
  · intro h x
    set U : Matrix (Fin k) (Fin k) ℂ := (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hUdef
    have hspec : A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
      have := hA.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at this
      simpa [hUdef] using this
    have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    set y := star U *ᵥ x with hy
    have hsy : star y = star x ᵥ* U := by
      rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    have e1 : star x ⬝ᵥ (A *ᵥ x) =
        star y ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
      have e0 := congrArg (fun B => B *ᵥ x) hspec
      rw [e0, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hsy]
    have e2 : star x ⬝ᵥ x = star y ⬝ᵥ y := by
      rw [hsy, ← Matrix.dotProduct_mulVec, hy, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    rw [e1, e2]
    simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp, Complex.re_sum, Pi.star_apply,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, RCLike.ofReal_re,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := h i
    have : ((RCLike.ofReal (hA.eigenvalues i) : ℂ)) = (hA.eigenvalues i : ℂ) := rfl
    simp only [this, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
    nlinarith [sq_nonneg (y i).re, sq_nonneg (y i).im,
      mul_le_mul_of_nonneg_right hi (add_nonneg (sq_nonneg (y i).re) (sq_nonneg (y i).im))]
  · intro h i
    set v := hA.eigenvectorBasis i with hv
    have hnorm : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
    have hvv : star (WithLp.ofLp v) ⬝ᵥ (WithLp.ofLp v) = 1 := by
      rw [dotProduct_comm]
      have : inner ℂ v v = (WithLp.ofLp v) ⬝ᵥ star (WithLp.ofLp v) :=
        EuclideanSpace.inner_eq_star_dotProduct v v
      rw [← this, inner_self_eq_norm_sq_to_K, hnorm]; simp
    have := h (WithLp.ofLp v)
    rw [hvv, Complex.one_re, mul_one] at this
    rw [hA.eigenvalues_eq i]
    simpa [hv] using this

open Matrix in
lemma isClosed_eig_le (M k : ℕ) (hk : 1 ≤ k) (ℓv : Fin k → ℝ) (c : ℝ) :
    IsClosed {Y : Fin M → Fin k → ℂ | SpikedWishart.Separated.largestEig M 1 ℓv Y ≤ c} := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : {Y : Fin M → Fin k → ℂ | SpikedWishart.Separated.largestEig M 1 ℓv Y ≤ c} =
      ⋂ x : Fin k → ℂ, {Y | (star x ⬝ᵥ (SpikedWishart.Separated.sampleCov M 1 ℓv Y *ᵥ x)).re ≤
        c * (star x ⬝ᵥ x).re} := by
    ext Y
    simp only [mem_setOf_eq, mem_iInter]
    unfold SpikedWishart.Separated.largestEig
    rw [ciSup_le_iff (Set.finite_range _).bddAbove]
    exact eig_le_iff _ _ c
  rw [this]
  refine isClosed_iInter fun x => isClosed_le ?_ continuous_const
  unfold SpikedWishart.Separated.sampleCov SpikedWishart.Separated.sampleVec
  fun_prop

lemma meas_eig (M k : ℕ) (hk : 1 ≤ k) (ℓv : Fin k → ℝ) :
    Measurable (fun Y : Fin M → Fin k → ℂ => SpikedWishart.Separated.largestEig M 1 ℓv Y) :=
  measurable_of_Iic fun c => (isClosed_eig_le M k hk ℓv c).measurableSet

lemma intI (k M : ℕ) (x : ℝ) :
    ∫ ξ in Set.pi univ (fun _ : Fin k => Icc (-Real.sqrt M) x),
        SpikedWishart.FixedDim.vandSq ξ * ∏ j, Real.exp (-Real.sqrt M * ξ j) * (1 + ξ j / Real.sqrt M) ^ (M - k)
      = ∫ ξ in Set.pi univ (fun _ : Fin k => Iic x), psi k M ξ := by
  have hpsi : psi k M = (Set.pi univ fun _ : Fin k => Ici (-Real.sqrt M)).indicator
      (fun ξ => SpikedWishart.FixedDim.vandSq ξ * ∏ j, phi k M (ξ j)) := by
    funext ξ
    unfold psi
    by_cases hξ : ξ ∈ Set.pi univ fun _ : Fin k => Ici (-Real.sqrt M)
    · rw [indicator_of_mem hξ]
      congr 1
      exact Finset.prod_congr rfl fun j _ => indicator_of_mem (hξ j (mem_univ j)) _
    · rw [indicator_of_notMem hξ]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hξ
      obtain ⟨j, hj⟩ := hξ
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (indicator_of_notMem hj _), mul_zero]
  rw [hpsi, setIntegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ici)]
  have hset : (Set.pi univ fun _ : Fin k => Iic x) ∩ (Set.pi univ fun _ : Fin k => Ici (-Real.sqrt M))
      = Set.pi univ (fun _ : Fin k => Icc (-Real.sqrt M) x) := by
    rw [← Set.pi_inter_distrib]
    congr 1
    funext j
    rw [inter_comm, Ici_inter_Iic]
  rw [hset]
  rfl

lemma ev_iff (a ℓ s x : ℝ) (hℓ : 0 < ℓ) (hs : 0 < s) :
    (a - ℓ) * (1 / ℓ) * s ≤ x ↔ a ≤ 1 / ℓ⁻¹ + x / (ℓ⁻¹ * s) := by
  have hℓ' := hℓ.ne'
  have hs' := hs.ne'
  rw [show 1 / ℓ⁻¹ + x / (ℓ⁻¹ * s) = ℓ + x * ℓ / s by field_simp,
    show (a - ℓ) * (1 / ℓ) * s = ((a - ℓ) * s) / ℓ by ring, div_le_iff₀ hℓ,
    ← sub_le_iff_le_add', le_div_iff₀ hs]

theorem main
    (H : ∀ (k M : ℕ), 1 ≤ k → k ≤ M → ∀ (π₁ : ℝ), 0 < π₁ → ∀ (x : ℝ), -Real.sqrt M ≤ x →
      (SpikedWishart.FixedDim.sampleLaw M k).real
          {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ 1 / π₁ + x / (π₁ * Real.sqrt M)} =
        Real.exp (-((k : ℝ) * M)) / (π₁ ^ (k * M) * (M : ℝ) ^ ((k : ℝ) ^ 2 / 2) * SpikedWishart.FixedDim.C M k π₁) *
          ∫ ξ in Set.pi univ (fun _ : Fin k => Icc (-Real.sqrt M) x),
            SpikedWishart.FixedDim.vandSq ξ * ∏ j, Real.exp (-Real.sqrt M * ξ j) * (1 + ξ j / Real.sqrt M) ^ (M - k))
    (k : ℕ) (hk : 1 ≤ k) (ℓ₁ : ℝ) (hℓ₁ : 0 < ℓ₁) :
    (∀ x : ℝ, Tendsto (fun M : ℕ => (SpikedWishart.FixedDim.sampleLaw M k).real
        {Y | (SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁) * (1 / ℓ₁) * Real.sqrt M ≤ x})
        atTop (𝓝 (SpikedWishart.FixedDim.G k x))) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun M : ℕ => (SpikedWishart.FixedDim.sampleLaw M k).real
        {Y | ε < |SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁|}) atTop (𝓝 0)) := by
  let X : (M : ℕ) → (Fin M → Fin k → ℂ) → ℝ := fun M Y =>
    (SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁) * (1 / ℓ₁) * Real.sqrt M
  let P : ℕ → ℝ → ℝ := fun M x => (SpikedWishart.FixedDim.sampleLaw M k).real {Y | X M Y ≤ x}
  let K : ℕ → ℝ := fun M => Real.exp (-((k : ℝ) * M)) /
      (ℓ₁⁻¹ ^ (k * M) * (M : ℝ) ^ ((k : ℝ) ^ 2 / 2) * SpikedWishart.FixedDim.C M k ℓ₁⁻¹)
  have hform : ∀ M : ℕ, max 1 (2 * k) ≤ M → ∀ x : ℝ, -Real.sqrt M ≤ x →
      P M x = K M * ∫ ξ in Set.pi univ (fun _ : Fin k => Iic x), psi k M ξ := by
    intro M hM x hx
    have hM1 : 1 ≤ M := le_of_max_le_left hM
    have hkM : k ≤ M := by have := le_of_max_le_right hM; omega
    have h := H k M hk hkM ℓ₁⁻¹ (inv_pos.mpr hℓ₁) x hx
    simp only [inv_inv] at h
    rw [intI] at h
    have hs0 : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast hM1)
    have hset : {Y : Fin M → Fin k → ℂ | X M Y ≤ x} =
        {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y ≤
          1 / ℓ₁⁻¹ + x / (ℓ₁⁻¹ * Real.sqrt M)} := by
      ext Y
      exact ev_iff _ _ _ _ hℓ₁ hs0
    show (SpikedWishart.FixedDim.sampleLaw M k).real {Y | X M Y ≤ x} = _
    rw [hset]
    exact h
  have hKT : ∀ M : ℕ, max 1 (2 * k) ≤ M → K M * ∫ ξ, psi k M ξ = 1 := by
    intro M hM
    have hmono : Monotone (fun n : ℕ => {Y : Fin M → Fin k → ℂ | X M Y ≤ n}) :=
      fun a b hab Y (hY : X M Y ≤ a) => (show X M Y ≤ (b : ℝ) from le_trans hY (Nat.cast_le.mpr hab))
    have hU : (⋃ n : ℕ, {Y : Fin M → Fin k → ℂ | X M Y ≤ n}) = univ :=
      eq_univ_of_forall fun Y => mem_iUnion.2 (exists_nat_ge (X M Y))
    have h1 := tendsto_measure_iUnion_atTop (μ := SpikedWishart.FixedDim.sampleLaw M k) hmono
    rw [hU, measure_univ] at h1
    have h1' : Tendsto (fun n : ℕ => P M n) atTop (𝓝 1) := by
      have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
      rw [ENNReal.toReal_one] at this
      exact this
    have h2 := tendsto_setIntegral_of_monotone (μ := volume) (f := psi k M)
      (fun n => MeasurableSet.univ_pi fun _ => measurableSet_Iic) (pi_Iic_mono k)
      (psi_integrable k M hM).integrableOn
    rw [iUnion_pi_Iic, setIntegral_univ] at h2
    have h3 : Tendsto (fun n : ℕ => P M n) atTop (𝓝 (K M * ∫ ξ, psi k M ξ)) := by
      refine (h2.const_mul (K M)).congr' (Eventually.of_forall fun n => ?_)
      have h0 : -Real.sqrt M ≤ (n : ℝ) := by
        have := Real.sqrt_nonneg (M : ℝ); have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      exact (hform M hM n h0).symm
    exact tendsto_nhds_unique h3 h1'
  have hT := psi_tendsto k univ
  simp only [setIntegral_univ] at hT
  have hK : Tendsto K atTop (𝓝 (SpikedWishart.FixedDim.Z k)⁻¹) := by
    rw [Z_eq]
    have := hT.inv₀ (by rw [← Z_eq]; exact (Z_pos k).ne')
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (max 1 (2 * k))] with M hM
    exact (eq_inv_of_mul_eq_one_left (hKT M hM)).symm
  have hP1 : ∀ x : ℝ, Tendsto (fun M => P M x) atTop (𝓝 (SpikedWishart.FixedDim.G k x)) := by
    intro x
    rw [G_eq]
    refine (hK.mul (psi_tendsto k _)).congr' ?_
    filter_upwards [eventually_ge_atTop (max 1 (2 * k)),
      tendsto_sqrt_nat.eventually_ge_atTop (-x)] with M hM hx
    exact (hform M hM x (by linarith)).symm
  refine ⟨hP1, ?_⟩
  intro ε hε
  have hXmeas : ∀ M : ℕ, Measurable (X M) := fun M =>
    (((meas_eig M k hk _).sub_const ℓ₁).mul_const _).mul_const _
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun M =>
    lt_of_lt_of_le ha measureReal_nonneg, fun δ hδ => ?_⟩
  obtain ⟨n, hn1, hn2⟩ := (((G_top k).eventually (lt_mem_nhds (show 1 - δ / 4 < 1 by linarith))).and
      ((G_bot k hk).eventually (gt_mem_nhds (show (0 : ℝ) < δ / 4 by linarith)))).exists
  have hA1 := (hP1 n).eventually (lt_mem_nhds (show 1 - δ / 2 < SpikedWishart.FixedDim.G k n by linarith))
  have hA2 := (hP1 (-n)).eventually
    (gt_mem_nhds (show SpikedWishart.FixedDim.G k (-n) < δ / 2 by linarith))
  filter_upwards [hA1, hA2, eventually_ge_atTop 1,
    tendsto_sqrt_nat.eventually_gt_atTop ((n : ℝ) * ℓ₁ / ε)] with M h1 h2 hM1 hsM
  have hs0 : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast hM1)
  have hAε : (n : ℝ) < ε * (1 / ℓ₁) * Real.sqrt M := by
    rw [div_lt_iff₀ hε] at hsM
    rw [show ε * (1 / ℓ₁) * Real.sqrt M = (Real.sqrt M * ε) / ℓ₁ by ring, lt_div_iff₀ hℓ₁]
    exact hsM
  have hsub : {Y : Fin M → Fin k → ℂ | ε < |SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁|}
      ⊆ {Y | X M Y ≤ n}ᶜ ∪ {Y | X M Y ≤ -n} := by
    intro Y hY
    simp only [mem_setOf_eq] at hY
    have hl : 0 < 1 / ℓ₁ := one_div_pos.mpr hℓ₁
    rcases lt_abs.mp hY with h | h
    · left
      simp only [mem_compl_iff, mem_setOf_eq, not_le, X]
      exact hAε.trans (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h hl) hs0)
    · right
      simp only [mem_setOf_eq, X]
      have : (SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁) * (1 / ℓ₁) * Real.sqrt M
          < (-ε) * (1 / ℓ₁) * Real.sqrt M :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (by linarith) hl) hs0
      linarith
  calc (SpikedWishart.FixedDim.sampleLaw M k).real
        {Y | ε < |SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁|}
      ≤ (SpikedWishart.FixedDim.sampleLaw M k).real ({Y | X M Y ≤ n}ᶜ ∪ {Y | X M Y ≤ -n}) :=
        measureReal_mono hsub
    _ ≤ (SpikedWishart.FixedDim.sampleLaw M k).real {Y | X M Y ≤ n}ᶜ +
          (SpikedWishart.FixedDim.sampleLaw M k).real {Y | X M Y ≤ -n} := measureReal_union_le _ _
    _ = (1 - P M n) + P M (-n) := by
        rw [probReal_compl_eq_one_sub (measurableSet_le (hXmeas M) measurable_const)]
    _ < δ := by linarith

end SWFDAux

open SpikedWishart.FixedDim MeasureTheory Filter Topology in
theorem solution (k : ℕ) (hk : 1 ≤ k) (ℓ₁ : ℝ) (hℓ₁ : 0 < ℓ₁) :
    (∀ x : ℝ, Tendsto (fun M : ℕ => (sampleLaw M k).real
        {Y | (SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁) * (1 / ℓ₁) * Real.sqrt M ≤ x})
        atTop (𝓝 (G k x))) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun M : ℕ => (sampleLaw M k).real
        {Y | ε < |SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁|}) atTop (𝓝 0)) := by
  exact SWFDAux.main SpikedWishart.FixedDim.eq_304 k hk ℓ₁ hℓ₁
