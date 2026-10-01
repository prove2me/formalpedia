-- Prove2me | solution 1 for ZudilinZeta.zudilin_lemma3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T09:53:08.593366+00:00
-- url     : https://prove2.me/submissions/76501a9a-347f-4d49-958a-9402aa8680b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZudilinZeta_zudilin_lcm_asymptotics
import Theorems.Thm_ZudilinZeta_zudilin_phi_log_growth_fixed
import Theorems.Thm_ZudilinZeta_zudilin_phi_tail_integral_eq
import Theorems.Thm_ZudilinZeta_zudilin_lemma2
import Theorems.Thm_ZudilinZeta_zudilin_saddle_log_side_conditions
import Theorems.Thm_ZudilinZeta_zudilin_small_values_criterion

open Filter ZudilinZeta
open scoped Topology

private lemma d_pos (N : ℕ) : 0 < (D N : ℝ) := by
  have h : D N ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro k hk
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
  exact_mod_cast Nat.pos_of_ne_zero h

private lemma phi_pos (P : Params) (n : ℕ) : 0 < (Phi P n : ℝ) := by
  have h : 0 < Phi P n := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Finset.mem_filter.mp hp).2.1.pos _
  exact_mod_cast h

private lemma denominator_log_tendsto (P : Params) :
    Tendsto (fun n : ℕ =>
      Real.log (((D (m P 1 * n) : ℝ) ^ P.r *
          ∏ j ∈ Finset.Icc 2 (P.q - P.r), (D (m P j * n) : ℝ)) /
        (Phi P n : ℝ)) / (n : ℝ)) atTop (𝓝 (C1 P)) := by
  have hq : 1 ≤ P.q - P.r := by have := P.q_ge; omega
  have hfirst := (zudilin_lcm_asymptotics P 1 le_rfl hq).const_mul (P.r : ℝ)
  have hsum : Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.Icc 2 (P.q - P.r), Real.log (D (m P j * n) : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ j ∈ Finset.Icc 2 (P.q - P.r), (m P j : ℝ))) := by
    apply tendsto_finsetSum
    intro j hj
    exact zudilin_lcm_asymptotics P j (by have := (Finset.mem_Icc.mp hj).1; omega)
      (Finset.mem_Icc.mp hj).2
  have hphi := zudilin_phi_log_growth_fixed P
  rw [zudilin_phi_tail_integral_eq P] at hphi
  unfold C1
  convert (hfirst.add hsum).sub hphi using 1
  funext n
  have hd : (D (m P 1 * n) : ℝ) ≠ 0 := (d_pos _).ne'
  have hp : (∏ j ∈ Finset.Icc 2 (P.q - P.r), (D (m P j * n) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => (d_pos _).ne')
  rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hd) hp) (phi_pos P n).ne',
    Real.log_mul (pow_ne_zero _ hd) hp, Real.log_pow,
    Real.log_prod (fun j _ => (d_pos (m P j * n)).ne'), sub_div, add_div,
    Finset.sum_div]
  ring

theorem solution (P : Params) (hr : P.r = 3) (τ₀ : ℂ)
    (hroot : charPoly P τ₀ = 0) (him : 0 < τ₀.im)
    (hmax : ∀ τ : ℂ, charPoly P τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re)
    (hre : τ₀.re < (P.eta 0 : ℝ)) (hpi : ∀ k : ℤ, (f0 P τ₀).im ≠ (k : ℝ) * Real.pi)
    (hC : C1 P < C0 P τ₀) :
    ∃ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), Irrational (zetaR (P.r + 2 * k)) := by
  let A : ℕ → ℝ := fun n =>
    ((D (m P 1 * n) : ℝ) ^ P.r *
        ∏ j ∈ Finset.Icc 2 (P.q - P.r), (D (m P j * n) : ℝ)) / (Phi P n : ℝ)
  have hApos (n : ℕ) : 0 < A n :=
    div_pos (mul_pos (pow_pos (d_pos _) _) (Finset.prod_pos (fun j _ => d_pos _)))
      (phi_pos P n)
  have hAlim : Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ)) atTop (𝓝 (C1 P)) :=
    denominator_log_tendsto P
  obtain ⟨hbounded, hnonzero⟩ :=
    zudilin_saddle_log_side_conditions P hr τ₀ hroot him hmax hre hpi
  have hlimsup := zudilin_lemma2 P hr τ₀ hroot him hmax hre hpi
  let δ : ℝ := (C0 P τ₀ - C1 P) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let c : ℝ := (C1 P - C0 P τ₀) / 2
  have hc : c < 0 := by dsimp [c]; linarith
  have hF : ∀ᶠ n : ℕ in atTop,
      Real.log |F P n| / (n : ℝ) < -C0 P τ₀ + δ := by
    apply eventually_lt_of_limsup_lt _ hbounded
    rw [hlimsup]
    dsimp [C0]
    linarith
  have hA : ∀ᶠ n : ℕ in atTop,
      Real.log (A n) / (n : ℝ) < C1 P + δ :=
    hAlim.eventually_lt_const (by linarith)
  have hexp : Tendsto (fun n : ℕ => Real.exp (c * (n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hc)
  apply zudilin_small_values_criterion P hr
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.exp (c * (n : ℝ)) < ε :=
    hexp.eventually_lt_const hε
  obtain ⟨n, hnzero, hnF, hnA, hnsmall, hnpos⟩ :=
    (hnonzero.and_eventually (hF.and (hA.and (hsmall.and (eventually_gt_atTop 0))))).exists
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hLambda : Lambda P n ≠ 0 := mul_ne_zero (hApos n).ne' hnzero
  have hlog : Real.log |Lambda P n| = Real.log (A n) + Real.log |F P n| := by
    change Real.log |A n * F P n| = _
    rw [abs_mul, abs_of_pos (hApos n), Real.log_mul (hApos n).ne' (abs_pos.mpr hnzero).ne']
  refine ⟨n, hnpos, hLambda, ?_⟩
  have hrate : Real.log |Lambda P n| / (n : ℝ) < c := by
    rw [hlog, add_div]
    dsimp [c, δ] at *
    linarith
  have hvalue : |Lambda P n| < Real.exp (c * (n : ℝ)) := by
    rw [← Real.exp_log (abs_pos.mpr hLambda)]
    exact Real.exp_lt_exp.mpr ((div_lt_iff₀ hn).mp hrate)
  exact hvalue.trans hnsmall
