-- Prove2me | solution 1 for SampleDrivenOS.Limit.theorem_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:45:33.82764+00:00
-- url     : https://prove2.me/submissions/82b567ff-2779-42cf-9418-2a084c82159b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting
import Theorems.Thm_SampleDrivenOS_Limit_lemma_6_iii
import Theorems.Thm_SampleDrivenOS_Limit_b8_h_limit
import Theorems.Thm_SampleDrivenOS_Limit_sdclpValue_le_alphaStar

open MeasureTheory Filter Topology

namespace Limit8Aux

/-- `b_i(p) = (i+2)p^{i+1} - (i+1)p^{i+2} ∈ [0,1]` for `p ∈ [0,1]`. -/
lemma b_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ℕ) :
    0 ≤ ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2) := by
  have h : ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)
      = p ^ (i + 1) * (((i : ℝ) + 2) - ((i : ℝ) + 1) * p) := by ring
  rw [h]
  apply mul_nonneg (pow_nonneg hp0 _)
  have : ((i : ℝ) + 1) * p ≤ (i : ℝ) + 1 := by
    have : (0:ℝ) ≤ (i : ℝ) + 1 := by positivity
    nlinarith
  linarith

lemma b_le_one (p : ℝ) (hp0 : 0 ≤ p) (i : ℕ) :
    ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2) ≤ 1 := by
  induction i with
  | zero =>
    simp
    nlinarith [sq_nonneg (p - 1)]
  | succ n ih =>
    have key : (((n + 1 : ℕ) : ℝ) + 2) * p ^ (n + 1 + 1) - (((n + 1 : ℕ) : ℝ) + 1) * p ^ (n + 1 + 2)
        = (((n : ℝ) + 2) * p ^ (n + 1) - ((n : ℝ) + 1) * p ^ (n + 2))
          - ((n : ℝ) + 2) * p ^ (n + 1) * (1 - p) ^ 2 := by
      push_cast; ring
    rw [key]
    have : 0 ≤ ((n : ℝ) + 2) * p ^ (n + 1) * (1 - p) ^ 2 := by positivity
    linarith

/-- the summand of (19) -/
noncomputable def term (p η : ℝ) (i : ℕ) : ℝ :=
  Real.log (1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2))) /
    (((i : ℝ) + 1) * ((i : ℝ) + 2))

lemma summable_w : Summable (fun i : ℕ => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
  have h2 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa using this
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h2
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma arg_bounds (p η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (i : ℕ) :
    1 - η ≤ 1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)) ∧
    1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)) ≤ 1 := by
  have h0 := b_nonneg p hp0 hp1 i
  have h1 := b_le_one p hp0 i
  constructor
  · nlinarith
  · nlinarith

lemma summable_term (p η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    Summable (term p η) := by
  refine Summable.of_norm_bounded (g := fun i : ℕ => (-Real.log (1 - η)) *
      (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)))) (summable_w.mul_left _) (fun i => ?_)
  obtain ⟨hlo, hhi⟩ := arg_bounds p η hp0 hp1 hη0 i
  have hpos : 0 < 1 - η := by linarith
  set x := 1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2))
  have hx0 : 0 < x := lt_of_lt_of_le hpos hlo
  have hlogle : Real.log x ≤ 0 := Real.log_nonpos hx0.le hhi
  have hloglo : Real.log (1 - η) ≤ Real.log x := Real.log_le_log hpos hlo
  have hd : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
  unfold term
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hd, abs_of_nonpos hlogle, div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma tsum_anti (p η η' : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (hηη' : η ≤ η')
    (hη'1 : η' < 1) : ∑' i, term p η' i ≤ ∑' i, term p η i := by
  apply Summable.tsum_le_tsum _ (summable_term p η' hp0 hp1 (by linarith) hη'1)
    (summable_term p η hp0 hp1 hη0 (by linarith))
  intro i
  unfold term
  have hd : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
  apply div_le_div_of_nonneg_right _ hd.le
  obtain ⟨hlo, -⟩ := arg_bounds p η' hp0 hp1 (by linarith) i
  have h1 := b_le_one p hp0 i
  apply Real.log_le_log (by linarith)
  nlinarith

/-- `g(η) = RHS(19) - LHS(19)` is antitone in `η`. -/
lemma g_anti (p η η' : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (hηη' : η ≤ η')
    (hη'1 : η' < 1) :
    ∑' i, term p η' i - (Real.log p + η' * (1 - p) ^ 2 / p) ≤
      ∑' i, term p η i - (Real.log p + η * (1 - p) ^ 2 / p) := by
  have h1 := tsum_anti p η η' hp0.le hp1 hη0 hηη' hη'1
  have h2 : η * (1 - p) ^ 2 / p ≤ η' * (1 - p) ^ 2 / p := by
    apply div_le_div_of_nonneg_right _ hp0.le
    exact mul_le_mul_of_nonneg_right hηη' (sq_nonneg _)
  linarith

lemma D_neg (p η : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    Real.log p + η * (1 - p) ^ 2 / p < 0 := by
  have hp0 : 0 < p := by linarith
  have hl : Real.log p ≤ p - 1 := Real.log_le_sub_one_of_pos hp0
  have : η * (1 - p) ^ 2 / p < 1 - p := by
    rw [div_lt_iff₀ hp0]
    have h1p : 0 < 1 - p := by linarith
    have : η * (1 - p) ^ 2 ≤ (1 - p) ^ 2 := by
      apply mul_le_of_le_one_left (sq_nonneg _) hη1.le
    nlinarith
  linarith

noncomputable def Iint (η : ℝ) : ℝ := ∫ y in (0:ℝ)..1, 1 / (y * (1 - Real.log y) + 1 / η - 1)

lemma cont_den (c : ℝ) : Continuous (fun y : ℝ => y * (1 - Real.log y) + c) := by
  have : (fun y : ℝ => y * (1 - Real.log y) + c) = fun y => y - y * Real.log y + c := by
    funext y; ring
  rw [this]
  exact (continuous_id.sub Real.continuous_mul_log).add continuous_const

lemma den_nonneg (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ y * (1 - Real.log y) := by
  have := Real.log_nonpos hy0 hy1
  exact mul_nonneg hy0 (by linarith)

lemma integrand_cont (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ContinuousOn (fun y : ℝ => 1 / (y * (1 - Real.log y) + 1 / η - 1)) (Set.Icc 0 1) := by
  have hc : 0 < 1 / η - 1 := by
    rw [sub_pos, lt_one_div (by norm_num) hη0]; simpa using hη1
  have : (fun y : ℝ => 1 / (y * (1 - Real.log y) + 1 / η - 1)) =
      fun y => 1 / (y * (1 - Real.log y) + (1 / η - 1)) := by funext y; ring_nf
  rw [this]
  apply ContinuousOn.div continuousOn_const (cont_den _).continuousOn
  intro y hy
  have := den_nonneg y hy.1 hy.2
  linarith

lemma Iint_lt (η η' : ℝ) (hη0 : 0 < η) (hηη' : η < η') (hη'1 : η' < 1) :
    Iint η < Iint η' := by
  unfold Iint
  have hc : ∀ e : ℝ, 0 < e → e < 1 → 0 < 1 / e - 1 := by
    intro e he0 he1
    rw [sub_pos, lt_one_div (by norm_num) he0]; simpa using he1
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 1, 1 / (y * (1 - Real.log y) + 1 / η - 1) <
      1 / (y * (1 - Real.log y) + 1 / η' - 1) := by
    intro y hy
    have hA := den_nonneg y hy.1 hy.2
    have h' := hc η' (by linarith) hη'1
    apply one_div_lt_one_div_of_lt (by linarith)
    have : 1 / η' < 1 / η := one_div_lt_one_div_of_lt hη0 hηη'
    linarith
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
    (integrand_cont η hη0 (by linarith)) (integrand_cont η' (by linarith) hη'1)
  · intro x hx; exact (hpt x ⟨hx.1.le, hx.2⟩).le
  · exact ⟨0, ⟨le_refl _, by norm_num⟩, hpt 0 ⟨le_refl _, by norm_num⟩⟩

end Limit8Aux

open Limit8Aux SampleDrivenOS.Limit in
theorem solution (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) (aT : ℝ → ℝ)
    (haT : ∀ p ∈ Set.Ioo (0:ℝ) 1, SampleDrivenOS.Limit.IsAlphaTilde p (aT p)) :
    (∀ p ∈ Set.Ioo (0:ℝ) 1, 0 ≤ aT p ∧ aT p ≤ SampleDrivenOS.Limit.sdclpValue p ∧
        SampleDrivenOS.Limit.sdclpValue p ≤ s) ∧
      Tendsto aT (𝓝[<] 1) (𝓝 s) ∧ Tendsto SampleDrivenOS.Limit.sdclpValue (𝓝[<] 1) (𝓝 s) := by
  obtain ⟨hs0, hs1, hsI⟩ := hs
  have hsI' : Iint s = 1 := hsI
  -- the root equation, in the `term` notation
  have hroot : ∀ p ∈ Set.Ioo (0:ℝ) 1,
      ∑' i, term p (aT p) i - (Real.log p + aT p * (1 - p) ^ 2 / p) = 0 := by
    intro p hp
    obtain ⟨-, -, h⟩ := haT p hp
    unfold term
    rw [← h]; ring
  -- part 1
  have part1 : ∀ p ∈ Set.Ioo (0:ℝ) 1, 0 ≤ aT p ∧ aT p ≤ sdclpValue p ∧ sdclpValue p ≤ s := by
    intro p hp
    obtain ⟨ha0, ha1, h⟩ := haT p hp
    refine ⟨ha0.le, ?_, sdclpValue_le_alphaStar p s hp ⟨hs0, hs1, hsI⟩⟩
    have hg : ∀ i : ℕ, gammaK p (aT p) (i + 2) =
        1 - aT p + aT p * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)) := by
      intro i
      simp only [gammaK]
      have : i + 2 - 1 = i + 1 := by omega
      rw [this]; push_cast; ring
    have h18 : Real.log p + aT p * (1 - p) ^ 2 / p ≤
        ∑' i : ℕ, Real.log (gammaK p (aT p) (i + 2)) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
      simp only [hg]
      rw [h]
    have hfeas := lemma_6_iii p (aT p) hp ⟨ha0, ha1⟩ h18
    unfold sdclpValue
    refine le_csSup ⟨1, ?_⟩ ⟨_, hfeas⟩
    rintro α ⟨q, hq⟩
    exact hq.2.2.1
  have hev : ∀ᶠ p in 𝓝[<] (1:ℝ), p ∈ Set.Ioo (1/2 : ℝ) 1 :=
    Ioo_mem_nhdsLT (by norm_num)
  -- lower bound
  have lower : ∀ η, 0 < η → η < s → ∀ᶠ p in 𝓝[<] (1:ℝ), η < aT p := by
    intro η hη0 hηs
    have hη1 : η < 1 := by linarith
    have hI : Iint η < 1 := hsI' ▸ Iint_lt η s hη0 hηs hs1
    have hlim := b8_h_limit η ⟨hη0, hη1⟩
    have hev2 : ∀ᶠ p in 𝓝[<] (1:ℝ), hFun p η < 1 := hlim (Iio_mem_nhds hI)
    filter_upwards [hev, hev2] with p hp hh
    have hp' : p ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
    have hD := D_neg p η hp.1 hp.2 hη0.le hη1
    have hN : Real.log p + η * (1 - p) ^ 2 / p < ∑' i, term p η i := by
      unfold hFun at hh
      rw [div_lt_one_of_neg hD] at hh
      exact hh
    by_contra hcon
    push Not at hcon
    have := g_anti p (aT p) η hp'.1 hp'.2.le (haT p hp').1.le hcon hη1
    have := hroot p hp'
    linarith
  have upper : ∀ η, s < η → η < 1 → ∀ᶠ p in 𝓝[<] (1:ℝ), aT p < η := by
    intro η hsη hη1
    have hη0 : 0 < η := by linarith
    have hI : 1 < Iint η := hsI' ▸ Iint_lt s η hs0 hsη hη1
    have hlim := b8_h_limit η ⟨hη0, hη1⟩
    have hev2 : ∀ᶠ p in 𝓝[<] (1:ℝ), 1 < hFun p η := hlim (Ioi_mem_nhds hI)
    filter_upwards [hev, hev2] with p hp hh
    have hp' : p ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
    have hD := D_neg p η hp.1 hp.2 hη0.le hη1
    have hN : ∑' i, term p η i < Real.log p + η * (1 - p) ^ 2 / p := by
      unfold hFun at hh
      rw [one_lt_div_of_neg hD] at hh
      exact hh
    by_contra hcon
    push Not at hcon
    have := g_anti p η (aT p) hp'.1 hp'.2.le hη0.le hcon (haT p hp').2.1
    have := hroot p hp'
    linarith
  have hT : Tendsto aT (𝓝[<] 1) (𝓝 s) := by
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have h := lower (max a (s / 2)) (lt_max_of_lt_right (by linarith))
        (max_lt ha (by linarith))
      filter_upwards [h] with p hp
      exact lt_of_le_of_lt (le_max_left _ _) hp
    · have h := upper (min b ((s + 1) / 2)) (lt_min hb (by linarith))
        (lt_of_le_of_lt (min_le_right _ _) (by linarith))
      filter_upwards [h] with p hp
      exact lt_of_lt_of_le hp (min_le_left _ _)
  refine ⟨part1, hT, ?_⟩
  have hev3 : ∀ᶠ p in 𝓝[<] (1:ℝ), p ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hT tendsto_const_nhds
  · filter_upwards [hev3] with p hp using (part1 p hp).2.1
  · filter_upwards [hev3] with p hp using (part1 p hp).2.2
