-- Prove2me | solution 1 for ValueTrial.Asymptotic.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:23:18.717503+00:00
-- url     : https://prove2.me/submissions/a2ccf893-5904-4302-903e-d512e89cfffb

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model
import Theorems.Thm_ValueTrial_Asymptotic_lemma_EC_1
import Theorems.Thm_ValueTrial_Asymptotic_lemma_EC_2
import Theorems.Thm_ValueTrial_Asymptotic_lemma_EC_3
import Theorems.Thm_ValueTrial_Asymptotic_lemma_EC_4

open MeasureTheory ProbabilityTheory Filter

namespace VT5Aux

lemma integrable_pos (x : ℝ) :
    Integrable (fun v : ℝ => max (v - x) 0) (gaussianReal 0 1) := by
  have h1 : Integrable (fun v : ℝ => v) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  exact (h1.sub (integrable_const x)).pos_part

lemma nl_eq (x : ℝ) :
    InventoryControl.normalLoss x = ∫ v, max (v - x) 0 ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, InventoryControl.normalLoss]
  have h1 : ∫ v in Set.Ioi x, (v - x) * gaussianPDFReal 0 1 v
      = ∫ v in Set.Ioi x, gaussianPDFReal 0 1 v • max (v - x) 0 := by
    refine setIntegral_congr_fun (measurableSet_Ioi (a := x)) ?_
    intro v hv
    simp only [Set.mem_Ioi] at hv
    simp only [smul_eq_mul]
    rw [max_eq_left (by linarith)]; ring
  rw [h1]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
  intro v hv
  simp only [Set.mem_Ioi, not_lt] at hv
  rw [max_eq_right (by linarith : v - x ≤ 0)]; simp

lemma nl_neg (x : ℝ) :
    InventoryControl.normalLoss (-x) = InventoryControl.normalLoss x + x := by
  rw [nl_eq, nl_eq]
  have hsymm : ∫ v, max (v - x) 0 ∂(gaussianReal 0 1)
      = ∫ v, max (-v - x) 0 ∂(gaussianReal 0 1) := by
    conv_lhs => rw [show (gaussianReal 0 1) = (gaussianReal 0 1).map (fun v : ℝ => -v) by
      rw [gaussianReal_map_neg, neg_zero]]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have h1 : Integrable (fun v : ℝ => v) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  have hA : Integrable (fun v : ℝ => max (v - -x) 0) (gaussianReal 0 1) := integrable_pos (-x)
  have hB : Integrable (fun v : ℝ => max (-v - x) 0) (gaussianReal 0 1) :=
    ((h1.neg).sub (integrable_const x)).pos_part
  have key : ∫ v, max (v - -x) 0 ∂(gaussianReal 0 1) - ∫ v, max (-v - x) 0 ∂(gaussianReal 0 1)
      = x := by
    rw [← integral_sub hA hB]
    have : (fun v : ℝ => max (v - -x) 0 - max (-v - x) 0) = fun v => v + x := by
      funext v
      rcases le_total 0 (v + x) with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    rw [this, integral_add h1 (integrable_const x), integral_id_gaussianReal]
    simp
  rw [hsymm]; linarith

lemma nl_nonneg (x : ℝ) : 0 ≤ InventoryControl.normalLoss x := by
  rw [nl_eq]
  exact integral_nonneg (fun v => le_max_right _ _)

lemma nl_pos (x : ℝ) : 0 < InventoryControl.normalLoss x := by
  rw [nl_eq, integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hint : Integrable (fun v : ℝ => gaussianPDFReal 0 1 v • max (v - x) 0) := by
    have := integrable_pos x
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero] at this
    rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at this
    simpa only [toReal_gaussianPDF] using this
  rw [integral_pos_iff_support_of_nonneg _ hint]
  · have hsupp : Function.support (fun v : ℝ => gaussianPDFReal 0 1 v • max (v - x) 0)
        = Set.Ioi x := by
      ext v
      simp only [Function.mem_support, smul_eq_mul, Set.mem_Ioi, ne_eq, mul_eq_zero, not_or]
      constructor
      · rintro ⟨_, h⟩
        by_contra hv
        exact h (max_eq_right (by linarith [not_lt.mp hv]))
      · intro hv
        refine ⟨(gaussianPDFReal_pos 0 1 v one_ne_zero).ne', ?_⟩
        rw [max_eq_left (by linarith)]; linarith
    rw [hsupp, Real.volume_Ioi]; simp
  · intro v
    exact smul_nonneg (gaussianPDFReal_nonneg 0 1 v) (le_max_right _ _)

end VT5Aux

open ValueTrial.Asymptotic

theorem solution (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (cfix cr : ℝ)
    (hcfix : 0 ≤ cfix) (hcr : 0 ≤ cr) (hC : 0 < Cnet θ) :
    -- Case I: cr = 0, fixed patient pool, r = rmax
    (cr = 0 → ∀ rmax : ℝ, 0 < rmax → rmax ≤ θ.zeta →
      (∀ᶠ P in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P)) {x | 0 ≤ x.1 ∧ x.2 = rmax} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ P in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P))
            {x | 0 ≤ x.1 ∧ x.2 = rmax} (xs P)) →
        Tendsto (fun P => (xs P).1 * (xs P).2 / 2 / Real.sqrt P) atTop
            (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / (4 * Cnet θ)))) ∧
          Tendsto (fun P => V θ (fun r => cfix + cr * r) (fixedPool P) (xs P) / P) atTop
            (nhds (vInf θ))) ∧
    -- Case III (constant corrected): cr > 0, fixed patient pool, T = Tmax
    (0 < cr → ∀ Tmax : ℝ, 0 < Tmax →
      (∀ᶠ P in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P)) {x | x.1 = Tmax ∧ 0 ≤ x.2} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ P in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P))
            {x | x.1 = Tmax ∧ 0 ≤ x.2} (xs P)) →
        Tendsto (fun P => (xs P).1 * (xs P).2 / 2 / Real.sqrt P) atTop
            (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
              (4 * (Cnet θ + cr / Tmax))))) ∧
          Tendsto (fun P => V θ (fun r => cfix + cr * r) (fixedPool P) (xs P) / P) atTop
            (nhds (vInf θ))) ∧
    -- Case II: cr = 0, fixed horizon, r = rmax
    (cr = 0 → ∀ rmax : ℝ, 0 < rmax → rmax ≤ θ.zeta →
      (∀ᶠ H in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ H in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} (xs H)) →
        Tendsto (fun H => V θ (fun r => cfix + cr * r) (fixedHorizon θ H) (xs H) /
            (θ.zeta * (H - θ.Del))) atTop (nhds (vInf θ)) ∧
          Tendsto (fun H => (xs H).1 * (xs H).2 / 2 / Real.sqrt (θ.zeta * (H - θ.Del))) atTop
            (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
              (4 * Cnet θ + 4 * θ.zeta * sig0 θ *
                (InventoryControl.normalLoss (θ.mu0 / sig0 θ)
                  + (1 - θ.pN) * θ.mu0 / sig0 θ) / rmax))))) ∧
    -- Case IV: cr > 0, fixed horizon, T and r free
    (0 < cr →
      (∀ᶠ H in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ 0 ≤ x.2} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ H in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ 0 ≤ x.2} (xs H)) →
        Tendsto (fun H => V θ (fun r => cfix + cr * r) (fixedHorizon θ H) (xs H) /
            (θ.zeta * (H - θ.Del))) atTop (nhds (vInf θ)) ∧
          Tendsto (fun H => (xs H).1 * (xs H).2 / 2 / Real.sqrt (θ.zeta * (H - θ.Del))) atTop
            (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / (4 * Cnet θ))))) := by
  classical
  obtain ⟨hpN0, hpN1, hsX, hn0, hc0, hdon, hIN, hIS, hzeta, hDel, hrho0, hrho1⟩ := hS
  have hS' : θ.Standing := ⟨hpN0, hpN1, hsX, hn0, hc0, hdon, hIN, hIS, hzeta, hDel, hrho0, hrho1⟩
  -- basic constants
  set B : ℝ := Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ with hB
  have hBnn : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (gaussianPDFReal_nonneg _ _ _)
  have hsig0 : 0 < sig0 θ := div_pos hsX (Real.sqrt_pos.mpr hn0)
  set m : ℝ := θ.mu0 / sig0 θ with hm
  set Y : ℝ := InventoryControl.normalLoss m + (1 - θ.pN) * θ.mu0 / sig0 θ with hY
  have hYeq : Y = θ.pN * InventoryControl.normalLoss m
      + (1 - θ.pN) * InventoryControl.normalLoss (-m) := by
    rw [hY, VT5Aux.nl_neg, hm]; ring
  have hYpos : 0 < Y := by
    rw [hYeq]
    have h1 := VT5Aux.nl_pos m
    have h2 := VT5Aux.nl_pos (-m)
    have : 0 < 1 - θ.pN := by linarith
    nlinarith [mul_pos this h2, mul_nonneg hpN0 h1.le]
  have hvInf : vInf θ = sig0 θ * Y := by
    rw [hYeq, vInf]; ring
  -- V depends only on T * r for constant setup cost and a fixed pool
  have hVprod : ∀ (k P : ℝ) (x y : ℝ × ℝ), x.1 * x.2 = y.1 * y.2 →
      V θ (fun _ => k) (fixedPool P) x = V θ (fun _ => k) (fixedPool P) y := by
    intro k P x y hxy
    simp only [V, Ttil, Prho, hρ, if_true, fixedPool, zero_mul, neg_zero, Real.exp_zero, one_mul]
    rw [hxy, show θ.c * x.1 * x.2 = θ.c * (y.1 * y.2) by rw [← hxy]; ring,
      show θ.c * y.1 * y.2 = θ.c * (y.1 * y.2) by ring]
  have hfun0 : cr = 0 → (fun r : ℝ => cfix + cr * r) = fun _ => cfix := by
    intro h; funext r; simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Case I
    intro hcr0 rmax hrmax _
    rw [hfun0 hcr0]
    have hEC := lemma_EC_1 θ hS' hρ cfix hcfix hC
    -- optimality on the line r = rmax is optimality on the quadrant
    have hline : ∀ (P : ℝ) (x : ℝ × ℝ),
        IsOptOn (V θ (fun _ => cfix) (fixedPool P)) (Set.Ici 0 ×ˢ Set.Ici 0) x →
        IsOptOn (V θ (fun _ => cfix) (fixedPool P)) {x | 0 ≤ x.1 ∧ x.2 = rmax}
          (x.1 * x.2 / rmax, rmax) := by
      intro P x hx
      obtain ⟨⟨hx1, hx2⟩, hxopt⟩ := hx
      simp only [Set.mem_Ici] at hx1 hx2
      refine ⟨⟨div_nonneg (mul_nonneg hx1 hx2) hrmax.le, rfl⟩, ?_⟩
      intro y hy
      rw [hVprod cfix P (x.1 * x.2 / rmax, rmax) x (by field_simp)]
      exact hxopt y ⟨Set.mem_Ici.mpr hy.1, Set.mem_Ici.mpr (hy.2 ▸ hrmax.le)⟩
    have hquad : ∀ (P : ℝ) (x : ℝ × ℝ),
        IsOptOn (V θ (fun _ => cfix) (fixedPool P)) {x | 0 ≤ x.1 ∧ x.2 = rmax} x →
        IsOptOn (V θ (fun _ => cfix) (fixedPool P)) (Set.Ici 0 ×ˢ Set.Ici 0) x := by
      intro P x hx
      obtain ⟨⟨hx1, hx2⟩, hxopt⟩ := hx
      refine ⟨⟨Set.mem_Ici.mpr hx1, Set.mem_Ici.mpr (hx2 ▸ hrmax.le)⟩, ?_⟩
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      simp only [Set.mem_Ici] at hy1 hy2
      rw [hVprod cfix P y (y.1 * y.2 / rmax, rmax) (by field_simp)]
      exact hxopt _ ⟨div_nonneg (mul_nonneg hy1 hy2) hrmax.le, rfl⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [hEC.1] with P hP
      obtain ⟨x, hx⟩ := hP
      exact ⟨_, hline P x hx⟩
    · intro xs hxs
      exact hEC.2 xs (hxs.mono fun P hP => hquad P (xs P) hP)
  · -- Case III
    intro hcr Tmax hTmax
    have hEC := lemma_EC_3 θ hS' hρ cfix cr hcfix hcr Tmax hTmax hC
    refine ⟨hEC.1, ?_⟩
    intro xs hxs
    have h := hEC.2 xs hxs
    have hD : Tmax * (θ.c * Tmax + cr - θ.don * (1 - 2 * θ.pN) * θ.mu0 * Tmax / 2)
        = Tmax * (Tmax * Cnet θ + cr) := by rw [Cnet]; ring
    have hDpos : 0 < Tmax * Cnet θ + cr := by positivity
    have hconst : Tmax / 2 * Real.sqrt (B /
        (Tmax * (θ.c * Tmax + cr - θ.don * (1 - 2 * θ.pN) * θ.mu0 * Tmax / 2)))
        = Real.sqrt (B / (4 * (Cnet θ + cr / Tmax))) := by
      rw [show Tmax / 2 = Real.sqrt ((Tmax / 2) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm, ← Real.sqrt_mul (sq_nonneg _), hD]
      congr 1
      field_simp
      ring
    refine ⟨?_, by rw [hvInf]; exact h.2⟩
    rw [← hconst]
    refine (h.1.const_mul (Tmax / 2)).congr' ?_
    filter_upwards [hxs] with P hP
    rw [hP.1.1]; ring
  · -- Case II
    intro hcr0 rmax hrmax hrz
    rw [hfun0 hcr0]
    have hEC := lemma_EC_2 θ hS' hρ cfix hcfix rmax hrmax hrz hC
    refine ⟨hEC.1, ?_⟩
    intro xs hxs
    have h := hEC.2 xs hxs
    refine ⟨h.2, ?_⟩
    have hDpos : 0 < Cnet θ * rmax ^ 2 + θ.zeta * rmax * sig0 θ * Y := by positivity
    have hconst : rmax / 2 * Real.sqrt (B /
        (Cnet θ * rmax ^ 2 + θ.zeta * rmax * sig0 θ * Y))
        = Real.sqrt (B / (4 * Cnet θ + 4 * θ.zeta * sig0 θ * Y / rmax)) := by
      rw [show rmax / 2 = Real.sqrt ((rmax / 2) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm, ← Real.sqrt_mul (sq_nonneg _)]
      congr 1
      field_simp
      ring
    rw [← hconst]
    refine (h.1.const_mul (rmax / 2)).congr' ?_
    filter_upwards [hxs] with H hH
    rw [hH.1.2.2]; ring
  · -- Case IV
    intro hcr
    have hEC := lemma_EC_4 θ hS' hρ cfix cr hcfix hcr
    dsimp only at hEC
    have hK : θ.sigX * θ.zeta * Y / (Real.sqrt θ.n0 * cr) = θ.zeta * sig0 θ * Y / cr := by
      rw [sig0]; field_simp
    rw [hK] at hEC
    set K : ℝ := θ.zeta * sig0 θ * Y / cr with hKdef
    have hKpos : 0 < K := by positivity
    have ha := hEC.1 hC.le
    refine ⟨ha.1, ?_⟩
    intro xs hxs
    refine ⟨ha.2 xs hxs, ?_⟩
    have hb := hEC.2 hC xs hxs
    set L : ℝ := (K ^ 2 * Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / Cnet θ) ^ ((1 : ℝ) / 4)
      with hL
    have hLL : L * L / (2 * K) = Real.sqrt (B / (4 * Cnet θ)) := by
      have hnn : 0 ≤ K ^ 2 * Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / Cnet θ := by
        have := hBnn; rw [hB] at this
        rw [mul_assoc]; positivity
      rw [hL, ← Real.rpow_add' hnn (by norm_num), show (1 : ℝ) / 4 + 1 / 4 = 1 / 2 by norm_num,
        ← Real.sqrt_eq_rpow, mul_assoc, mul_div_assoc, Real.sqrt_mul (sq_nonneg K),
        Real.sqrt_sq hKpos.le, ← hB,
        show B / (4 * Cnet θ) = (B / Cnet θ) / 2 ^ 2 by ring,
        Real.sqrt_div' (B / Cnet θ) (by positivity : (0:ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    rw [← hLL]
    refine ((hb.1.mul hb.2).div_const (2 * K)).congr' ?_
    have hev : ∀ᶠ H in atTop, 0 < θ.zeta * (H - θ.Del) :=
      (eventually_gt_atTop θ.Del).mono fun H hH => mul_pos hzeta (by linarith)
    filter_upwards [hev] with H hX
    have hX4 : (θ.zeta * (H - θ.Del)) ^ ((1 : ℝ) / 4) * (θ.zeta * (H - θ.Del)) ^ ((1 : ℝ) / 4)
        = Real.sqrt (θ.zeta * (H - θ.Del)) := by
      rw [← Real.rpow_add hX, Real.sqrt_eq_rpow]; norm_num
    have hX4pos : 0 < (θ.zeta * (H - θ.Del)) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hX _
    rw [div_mul_div_comm, hX4]
    field_simp
