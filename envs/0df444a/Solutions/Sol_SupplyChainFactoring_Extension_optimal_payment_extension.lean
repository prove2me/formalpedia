-- Prove2me | solution 1 for SupplyChainFactoring.Extension.optimal_payment_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T17:10:14.557562+00:00
-- url     : https://prove2.me/submissions/af9e4247-0bc4-41ad-94af-40b390abb1b7

import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

set_option autoImplicit false

namespace P874

open SupplyChainFactoring.Extension MeasureTheory ProbabilityTheory Filter Topology

variable (M : Model)

lemma cdf_zero : cdf M.μ 0 = 0 := by
  have := M.isProb
  rw [cdf_eq_real, measureReal_def]
  have : M.μ (Set.Iic 0) = 0 := by
    rw [M.density, withDensity_apply _ measurableSet_Iic,
      setLIntegral_congr (Iio_ae_eq_Iic (a := (0:ℝ))).symm,
      setLIntegral_congr_fun measurableSet_Iio
        (g := fun _ => (0 : ENNReal)) (fun x hx => by simp [M.f_zero_of_neg x hx])]
    simp
  rw [this]; simp

lemma cdf_pos {x : ℝ} (hx : 0 < x) : 0 < cdf M.μ x := by
  have := M.isProb
  obtain ⟨ε0, h0, hZ⟩ := EReal.lt_iff_exists_real_btwn.mp M.Z_pos
  have h0' : (0:ℝ) < ε0 := by exact_mod_cast h0
  have hε : 0 < min x ε0 := lt_min hx h0'
  have hsub : Set.Icc 0 (min x ε0) ⊆ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ M.Z} := by
    intro y hy
    refine ⟨hy.1, le_trans ?_ hZ.le⟩
    exact_mod_cast hy.2.trans (min_le_right _ _)
  obtain ⟨y0, hy0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hε.le)
    (M.f_continuousOn.mono hsub)
  have hδ : 0 < M.f y0 := M.f_pos y0 (hsub hy0).1 (hsub hy0).2
  rw [cdf_eq_real, measureReal_def]
  apply ENNReal.toReal_pos
  · rw [M.density, withDensity_apply _ measurableSet_Iic]
    apply ne_of_gt
    calc (0:ENNReal) < ENNReal.ofReal (M.f y0) * volume (Set.Icc 0 (min x ε0)) := by
          simp [hδ, hx, h0']
      _ = ∫⁻ _ in Set.Icc 0 (min x ε0), ENNReal.ofReal (M.f y0) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ y in Set.Icc 0 (min x ε0), ENNReal.ofReal (M.f y) :=
          setLIntegral_mono' measurableSet_Icc (fun y hy => ENNReal.ofReal_le_ofReal (hmin hy))
      _ ≤ ∫⁻ y in Set.Iic x, ENNReal.ofReal (M.f y) :=
          lintegral_mono_set (fun y hy => hy.2.trans (min_le_left _ _))
  · exact measure_ne_top _ _

lemma Fbar_anti : Antitone M.Fbar := fun x y h => by
  unfold Model.Fbar; linarith [monotone_cdf M.μ h]

lemma Fbar_le_one (x : ℝ) : M.Fbar x ≤ 1 := by
  unfold Model.Fbar; linarith [cdf_nonneg M.μ x]

lemma Fbar_nonneg (x : ℝ) : 0 ≤ M.Fbar x := by
  unfold Model.Fbar; linarith [cdf_le_one M.μ x]

lemma Fbar_lt_one {x : ℝ} (hx : 0 < x) : M.Fbar x < 1 := by
  unfold Model.Fbar; linarith [cdf_pos M hx]

lemma Fbar_tendsto : Tendsto M.Fbar atTop (𝓝 0) := by
  have := M.isProb
  have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_cdf_atTop M.μ)
  have hF : M.Fbar = fun x => 1 - cdf M.μ x := rfl
  rw [hF]; simpa using h2

lemma exists_Fbar_near_zero {r : ℝ} (hr : r < 1) : ∃ q, 0 < q ∧ r < M.Fbar q := by
  have hc := (cdf M.μ).right_continuous 0
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc (1 - r) (by linarith)
  refine ⟨δ / 2, by linarith, ?_⟩
  have h1 := h (show δ / 2 ∈ Set.Ici (0:ℝ) by simp only [Set.mem_Ici]; linarith)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  rw [cdf_zero, Real.dist_eq, sub_zero] at h1
  unfold Model.Fbar
  have := (abs_lt.mp h1).2
  linarith

lemma Fbar_ii (a b : ℝ) : IntervalIntegrable M.Fbar volume a b :=
  (Fbar_anti M).intervalIntegrable

lemma S_zero : M.S 0 = 0 := by simp [Model.S]

lemma S_sub (q1 q2 : ℝ) : M.S q2 - M.S q1 = ∫ ξ in q1..q2, M.Fbar ξ := by
  unfold Model.S
  rw [intervalIntegral.integral_interval_sub_left (Fbar_ii M _ _) (Fbar_ii M _ _)]

lemma S_inc_le {q1 q2 : ℝ} (h : q1 ≤ q2) : M.S q2 - M.S q1 ≤ (q2 - q1) * M.Fbar q1 := by
  rw [S_sub]
  have := intervalIntegral.integral_mono_on h (Fbar_ii M q1 q2)
    (intervalIntegrable_const (c := M.Fbar q1)) (fun x hx => Fbar_anti M hx.1)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this

lemma S_inc_ge {q1 q2 : ℝ} (h : q1 ≤ q2) : (q2 - q1) * M.Fbar q2 ≤ M.S q2 - M.S q1 := by
  rw [S_sub]
  have := intervalIntegral.integral_mono_on h
    (intervalIntegrable_const (c := M.Fbar q2)) (Fbar_ii M q1 q2) (fun x hx => Fbar_anti M hx.2)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this

lemma S_ge {q : ℝ} (hq : 0 ≤ q) : q * M.Fbar q ≤ M.S q := by
  have := S_inc_ge M hq
  rw [S_zero] at this; linarith

lemma S_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ M.S q :=
  le_trans (mul_nonneg hq (Fbar_nonneg M q)) (S_ge M hq)

lemma S_lt {q : ℝ} (hq : 0 < q) : M.S q < q := by
  have h1 := S_inc_le M (show 0 ≤ q / 2 by linarith)
  have h2 := S_inc_le M (show q / 2 ≤ q by linarith)
  rw [S_zero] at h1
  have h3 := Fbar_le_one M 0
  have h4 := Fbar_lt_one M (show 0 < q / 2 by linarith)
  have h5 : (q - q / 2) * M.Fbar (q / 2) < (q - q / 2) * 1 :=
    mul_lt_mul_of_pos_left h4 (by linarith)
  have h6 : (q / 2 - 0) * M.Fbar 0 ≤ (q / 2 - 0) * 1 :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  linarith

lemma S_cont : Continuous M.S := by
  unfold Model.S
  exact intervalIntegral.continuous_primitive (Fbar_ii M) 0

lemma exists_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ q, 0 ≤ q ∧ ∀ q', 0 ≤ q' → a * M.S q' - b * q' ≤ a * M.S q - b * q := by
  have hev : ∀ᶠ Q in atTop, a * M.Fbar Q ≤ b ∧ 0 ≤ Q := by
    have h1 : Tendsto (fun Q => a * M.Fbar Q) atTop (𝓝 0) := by
      simpa using (Fbar_tendsto M).const_mul a
    exact (h1.eventually (ge_mem_nhds hb)).and (eventually_ge_atTop 0)
  obtain ⟨Q, hQ, hQ0⟩ := hev.exists
  have hcont : ContinuousOn (fun q => a * M.S q - b * q) (Set.Icc 0 Q) :=
    ((continuous_const.mul (S_cont M)).sub (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hQ0) hcont
  refine ⟨q, hq.1, fun q' hq' => ?_⟩
  rcases le_total q' Q with h | h
  · exact hmax ⟨hq', h⟩
  · have h1 := S_inc_le M h
    have h2 : a * M.S Q - b * Q ≤ a * M.S q - b * q := hmax ⟨hQ0, le_rfl⟩
    have h3 : a * (M.S q' - M.S Q) ≤ a * ((q' - Q) * M.Fbar Q) := mul_le_mul_of_nonneg_left h1 ha
    have h4 : (q' - Q) * (a * M.Fbar Q) ≤ (q' - Q) * b := mul_le_mul_of_nonneg_left hQ (by linarith)
    nlinarith

lemma exists_pos {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    ∃ q, 0 ≤ q ∧ 0 < a * M.S q - b * q := by
  have ha : 0 < a := by linarith
  obtain ⟨q, hq, hF⟩ := exists_Fbar_near_zero M (r := b / a) (by rw [div_lt_one ha]; exact hab)
  refine ⟨q, hq.le, ?_⟩
  have h1 := S_ge M hq.le
  have h2 : b < a * M.Fbar q := by rwa [div_lt_iff₀ ha, mul_comm] at hF
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_lt_mul_of_pos_left h2 hq]

lemma neg_of_le {a b q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hq : 0 < q) :
    a * M.S q - b * q < 0 := by
  have h1 := S_lt M hq
  rcases ha.eq_or_lt with h | h
  · subst h; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left h1 h, mul_le_mul_of_nonneg_right hab hq.le]

lemma prof_eq (Λ Cs w q : ℝ) : M.supplierProfit Λ Cs w q = (1 - M.ρ Cs) *
    ((Λ * Real.exp (-(M.lamS * M.t1)) * w) * M.S q - (M.c * Real.exp (M.η Cs * M.t1)) * q) := by
  unfold Model.supplierProfit; ring

lemma core {Λ0 Cs Cr ws qs : ℝ} (hK : 0 < 1 - M.ρ Cs) (hR : 0 < 1 - M.ρ Cr) (hΛ0 : 0 < Λ0)
    (hfeas : M.c * Real.exp (M.η Cs * M.t1) < M.p * Λ0 * Real.exp (-(M.lamS * M.t1)))
    (heq : M.IsEquilibrium Λ0 Cs Cr ws qs) :
    0 < M.supplierProfit Λ0 Cs ws qs ∧ ∀ Λ : ℝ,
      ((∃ q, M.IsBestResponse Λ Cs ws q ∧
        M.supplierProfit Λ0 Cs ws qs ≤ M.supplierProfit Λ Cs ws q) ↔ Λ0 ≤ Λ) := by
  obtain ⟨hws, ⟨hqs, hBR⟩, hopt⟩ := heq
  have he1 : 0 < Real.exp (-(M.lamS * M.t1)) := Real.exp_pos _
  have hb : 0 < M.c * Real.exp (M.η Cs * M.t1) := mul_pos M.c_pos (Real.exp_pos _)
  have hmaxs : ∀ q, 0 ≤ q →
      Λ0 * Real.exp (-(M.lamS * M.t1)) * ws * M.S q - M.c * Real.exp (M.η Cs * M.t1) * q ≤
      Λ0 * Real.exp (-(M.lamS * M.t1)) * ws * M.S qs - M.c * Real.exp (M.η Cs * M.t1) * qs := by
    intro q hq
    have := hBR q hq
    rw [prof_eq, prof_eq] at this
    exact le_of_mul_le_mul_left this hK
  have hpos : 0 < M.supplierProfit Λ0 Cs ws qs := by
    have hΛe : 0 < Λ0 * Real.exp (-(M.lamS * M.t1)) := mul_pos hΛ0 he1
    have hb' : M.c * Real.exp (M.η Cs * M.t1) / (Λ0 * Real.exp (-(M.lamS * M.t1))) < M.p := by
      rw [div_lt_iff₀ hΛe]; linarith
    have hd := div_pos hb hΛe
    obtain ⟨w', hw'⟩ : ∃ w', w' = (M.c * Real.exp (M.η Cs * M.t1) /
        (Λ0 * Real.exp (-(M.lamS * M.t1))) + M.p) / 2 := ⟨_, rfl⟩
    have hw'0 : 0 ≤ w' := by rw [hw']; linarith
    have hw'p : w' < M.p := by rw [hw']; linarith
    have ha' : M.c * Real.exp (M.η Cs * M.t1) < Λ0 * Real.exp (-(M.lamS * M.t1)) * w' := by
      have h2 : M.c * Real.exp (M.η Cs * M.t1) / (Λ0 * Real.exp (-(M.lamS * M.t1))) < w' := by
        rw [hw']; linarith
      rw [div_lt_iff₀ hΛe] at h2; linarith
    obtain ⟨q', hq', hmax'⟩ := exists_max M (a := Λ0 * Real.exp (-(M.lamS * M.t1)) * w')
      (mul_nonneg hΛe.le hw'0) hb
    obtain ⟨q0, hq0, hpos0⟩ := exists_pos M hb ha'
    have hg' := lt_of_lt_of_le hpos0 (hmax' q0 hq0)
    have hSq' : 0 < M.S q' := by
      by_contra hcon; replace hcon := not_lt.mp hcon
      have : Λ0 * Real.exp (-(M.lamS * M.t1)) * w' * M.S q' ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hΛe.le hw'0) hcon
      nlinarith
    have hBR' : M.IsBestResponse Λ0 Cs w' q' := ⟨hq', fun q'' hq'' => by
      rw [prof_eq, prof_eq]; exact mul_le_mul_of_nonneg_left (hmax' q'' hq'') hK.le⟩
    have hRet := hopt w' q' hw'0 hBR'
    have hRpos : 0 < M.retailerProfit Cr w' q' := by
      unfold Model.retailerProfit
      have : 0 < M.p - w' := by linarith
      have := Real.exp_pos (-(M.lamS * M.t1))
      positivity
    have hRs : 0 < M.retailerProfit Cr ws qs := lt_of_lt_of_le hRpos hRet
    have hSqs : 0 < M.S qs := by
      rcases (S_nonneg M hqs).eq_or_lt with h | h
      · exfalso; unfold Model.retailerProfit at hRs; rw [← h] at hRs; simp at hRs
      · exact h
    have hqs0 : 0 < qs := by
      rcases hqs.eq_or_lt with h | h
      · rw [← h, S_zero] at hSqs; exact absurd hSqs (lt_irrefl _)
      · exact h
    have hg : 0 < Λ0 * Real.exp (-(M.lamS * M.t1)) * ws * M.S qs -
        M.c * Real.exp (M.η Cs * M.t1) * qs := by
      rcases lt_or_ge (M.c * Real.exp (M.η Cs * M.t1)) (Λ0 * Real.exp (-(M.lamS * M.t1)) * ws)
        with h | h
      · obtain ⟨q1, hq1, hp1⟩ := exists_pos M hb h
        exact lt_of_lt_of_le hp1 (hmaxs q1 hq1)
      · exfalso
        have h1 := neg_of_le M (mul_nonneg hΛe.le hws) h hb hqs0
        have h2 := hmaxs 0 le_rfl
        rw [S_zero] at h2
        linarith
    rw [prof_eq]; exact mul_pos hK hg
  refine ⟨hpos, fun Λ => ⟨?_, ?_⟩⟩
  · rintro ⟨q, ⟨hq, -⟩, hle⟩
    by_contra hlt; replace hlt := not_le.mp hlt
    have h0 := hBR q hq
    have hp := hpos
    rw [prof_eq] at hp
    rw [prof_eq, prof_eq] at hle h0
    have hwS : 0 ≤ ws * M.S q := mul_nonneg hws (S_nonneg M hq)
    have hid : (1 - M.ρ Cs) * (Λ * Real.exp (-(M.lamS * M.t1)) * ws * M.S q -
        M.c * Real.exp (M.η Cs * M.t1) * q) =
        (1 - M.ρ Cs) * (Λ0 * Real.exp (-(M.lamS * M.t1)) * ws * M.S q -
        M.c * Real.exp (M.η Cs * M.t1) * q) -
        (1 - M.ρ Cs) * (Λ0 - Λ) * Real.exp (-(M.lamS * M.t1)) * (ws * M.S q) := by ring
    rcases hwS.eq_or_lt with h | h
    · have hid2 : (1 - M.ρ Cs) * (Λ * Real.exp (-(M.lamS * M.t1)) * ws * M.S q -
          M.c * Real.exp (M.η Cs * M.t1) * q) =
          -((1 - M.ρ Cs) * (M.c * Real.exp (M.η Cs * M.t1) * q)) := by
        have : Λ * Real.exp (-(M.lamS * M.t1)) * ws * M.S q =
            Λ * Real.exp (-(M.lamS * M.t1)) * (ws * M.S q) := by ring
        rw [this, ← h]; ring
      have : 0 ≤ (1 - M.ρ Cs) * (M.c * Real.exp (M.η Cs * M.t1) * q) :=
        mul_nonneg hK.le (mul_nonneg hb.le hq)
      linarith
    · have : 0 < (1 - M.ρ Cs) * (Λ0 - Λ) * Real.exp (-(M.lamS * M.t1)) * (ws * M.S q) :=
        mul_pos (mul_pos (mul_pos hK (by linarith)) he1) h
      linarith
  · intro hΛ
    obtain ⟨q, hq, hmax⟩ := exists_max M (a := Λ * Real.exp (-(M.lamS * M.t1)) * ws)
      (mul_nonneg (mul_nonneg (by linarith) he1.le) hws) hb
    refine ⟨q, ⟨hq, fun q' hq' => by
      rw [prof_eq, prof_eq]; exact mul_le_mul_of_nonneg_left (hmax q' hq') hK.le⟩, ?_⟩
    rw [prof_eq, prof_eq]
    apply mul_le_mul_of_nonneg_left _ hK.le
    have h1 := hmax qs hqs
    have hwS := mul_nonneg hws (S_nonneg M hqs)
    have h3 : 0 ≤ (Λ - Λ0) * Real.exp (-(M.lamS * M.t1)) * (ws * M.S qs) :=
      mul_nonneg (mul_nonneg (by linarith) he1.le) hwS
    have h4 : Λ * Real.exp (-(M.lamS * M.t1)) * ws * M.S qs -
        Λ0 * Real.exp (-(M.lamS * M.t1)) * ws * M.S qs =
        (Λ - Λ0) * Real.exp (-(M.lamS * M.t1)) * (ws * M.S qs) := by ring
    linarith

lemma one_sub_rho_pos {C : ℝ} (hC : C ∈ Set.Ioo M.Cmin M.Cmax) : 0 < 1 - M.ρ C := by
  have hm : (M.Cmin + C) / 2 ∈ Set.Ioo M.Cmin M.Cmax :=
    ⟨by linarith [hC.1], by linarith [hC.1, hC.2]⟩
  have h1 := M.ρ_strictAnti hm hC (by linarith [hC.1])
  have h2 := (M.ρ_mem _ hm).2
  linarith

lemma ΛF_lt {C1 C2 Cr : ℝ} (h1 : C1 ∈ Set.Ioo M.Cmin M.Cmax) (h2 : C2 ∈ Set.Ioo M.Cmin M.Cmax)
    (h : C1 < C2) : M.ΛF C1 Cr < M.ΛF C2 Cr := by
  unfold Model.ΛF
  have := M.ρ_strictAnti h1 h2 h
  have h3 : M.η C2 ≤ M.η C1 := M.η_antitone h1 h2 h.le
  have h4 : Real.exp (M.η C2 * M.t2) ≤ Real.exp (M.η C1 * M.t2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h3 M.t2_pos.le)
  linarith


lemma mu_singleton (x : ℝ) : M.μ {x} = 0 := by
  rw [M.density, withDensity_apply _ (measurableSet_singleton x)]
  exact setLIntegral_measure_zero _ _ (Real.volume_singleton)

lemma cdf_cont : Continuous (cdf M.μ) := by
  have := M.isProb
  rw [continuous_iff_continuousAt]; intro x
  rw [(cdf M.μ).mono.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h := (cdf M.μ).measure_singleton x
  rw [measure_cdf, mu_singleton] at h
  have h2 := (cdf M.μ).mono.leftLim_le (le_refl x)
  have h3 : cdf M.μ x - Function.leftLim (cdf M.μ) x ≤ 0 := ENNReal.ofReal_eq_zero.mp h.symm
  linarith

lemma Fbar_cont : Continuous M.Fbar :=
  show Continuous (fun x => 1 - cdf M.μ x) from continuous_const.sub (cdf_cont M)

lemma Fbar_eq_zero {q : ℝ} (hq : M.Z ≤ (q : EReal)) : M.Fbar q = 0 := by
  have := M.isProb
  have h0 : M.μ (Set.Ioi q) = 0 := by
    rw [M.density, withDensity_apply _ measurableSet_Ioi,
      setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ENNReal))
        (fun x hx => by
          have hx' : q < x := hx
          have : M.Z < (x : EReal) := lt_of_le_of_lt hq (by exact_mod_cast hx')
          simp [M.f_zero_of_gt x this])]
    simp
  have h1 : M.μ (Set.Iic q) = 1 :=
    (prob_compl_eq_zero_iff measurableSet_Iic).mp (by rw [Set.compl_Iic]; exact h0)
  unfold Model.Fbar
  rw [cdf_eq_real, measureReal_def, h1]; simp

lemma cdf_eq_int {z1 y : ℝ} (hz1 : (z1 : EReal) ≤ M.Z) (hy0 : 0 ≤ y) (hy1 : y ≤ z1) :
    cdf M.μ y = ∫ t in (0:ℝ)..y, M.f t := by
  have := M.isProb
  have hcont : ContinuousOn M.f (Set.Icc 0 y) := M.f_continuousOn.mono (fun t ht =>
    ⟨ht.1, le_trans (by exact_mod_cast ht.2.trans hy1) hz1⟩)
  have hint : IntegrableOn M.f (Set.Ioc 0 y) :=
    (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have h1 : M.μ (Set.Ioc 0 y) = ENNReal.ofReal (cdf M.μ y - cdf M.μ 0) := by
    rw [← (cdf M.μ).measure_Ioc, measure_cdf]
  have h2 : M.μ (Set.Ioc 0 y) = ENNReal.ofReal (∫ t in Set.Ioc 0 y, M.f t) := by
    rw [M.density, withDensity_apply _ measurableSet_Ioc,
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun t => by simpa using M.f_nonneg t))]
  rw [h1, cdf_zero, sub_zero] at h2
  rw [intervalIntegral.integral_of_le hy0]
  have hnn : 0 ≤ ∫ t in Set.Ioc 0 y, M.f t :=
    setIntegral_nonneg measurableSet_Ioc (fun t _ => M.f_nonneg t)
  exact (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _) hnn).mp h2

lemma cdf_hasDerivAt {x : ℝ} (hx : M.InSupport x) : HasDerivAt (cdf M.μ) (M.f x) x := by
  obtain ⟨z1, hxz, hz1⟩ := EReal.lt_iff_exists_real_btwn.mp hx.2
  have hxz' : x < z1 := by exact_mod_cast hxz
  have hcont : ContinuousOn M.f (Set.Icc 0 z1) := M.f_continuousOn.mono (fun t ht =>
    ⟨ht.1, le_trans (by exact_mod_cast ht.2) hz1.le⟩)
  have hI : IntervalIntegrable M.f volume 0 x :=
    ContinuousOn.intervalIntegrable_of_Icc hx.1.le (hcont.mono (Set.Icc_subset_Icc_right hxz'.le))
  have hO : Set.Ioo 0 z1 ∈ 𝓝 x := Ioo_mem_nhds hx.1 hxz'
  have hmeas : StronglyMeasurableAtFilter M.f (𝓝 x) :=
    (hcont.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x ⟨hx.1, hxz'⟩
  have hca : ContinuousAt M.f x := hcont.continuousAt (Icc_mem_nhds hx.1 hxz')
  have hd := intervalIntegral.integral_hasDerivAt_right hI hmeas hca
  apply hd.congr_of_eventuallyEq
  filter_upwards [hO] with y hy
  exact cdf_eq_int M hz1.le hy.1.le hy.2.le

lemma Fbar_hasDerivAt {x : ℝ} (hx : M.InSupport x) : HasDerivAt M.Fbar (-M.f x) x :=
  show HasDerivAt (fun y => 1 - cdf M.μ y) (-M.f x) x from (cdf_hasDerivAt M hx).const_sub 1

lemma Fbar_strict {x y : ℝ} (hx : M.InSupport x) (hy : M.InSupport y) (h : x < y) :
    M.Fbar y < M.Fbar x := by
  have hsub : ∀ t ∈ Set.Icc x y, M.InSupport t := fun t ht =>
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt (by exact_mod_cast ht.2) hy.2⟩
  have := strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc x y) (f' := fun t => -M.f t)
    (Fbar_cont M).continuousOn
    (fun t ht => (Fbar_hasDerivAt M (hsub t (interior_subset ht))).hasDerivWithinAt)
    (fun t ht => by
      have := M.f_pos t (hsub t (interior_subset ht)).1.le (hsub t (interior_subset ht)).2.le
      linarith)
  exact this ⟨le_refl x, h.le⟩ ⟨h.le, le_refl y⟩ h

lemma S_hasDerivAt (x : ℝ) : HasDerivAt M.S (M.Fbar x) x :=
  show HasDerivAt (fun u => ∫ ξ in (0:ℝ)..u, M.Fbar ξ) (M.Fbar x) x from
    intervalIntegral.integral_hasDerivAt_right (Fbar_ii M 0 x)
      ((Fbar_cont M).stronglyMeasurableAtFilter _ _) (Fbar_cont M).continuousAt

lemma focn {a b q : ℝ} (hb : 0 < b) (hab : b < a) (hq : 0 ≤ q)
    (hmax : ∀ q', 0 ≤ q' → a * M.S q' - b * q' ≤ a * M.S q - b * q) :
    M.InSupport q ∧ a * M.Fbar q = b := by
  have ha : 0 < a := by linarith
  obtain ⟨q1, hq1, hp1⟩ := exists_pos M hb hab
  have hgq : 0 < a * M.S q - b * q := lt_of_lt_of_le hp1 (hmax q1 hq1)
  have hq0 : 0 < q := by
    rcases hq.eq_or_lt with h | h
    · rw [← h, S_zero] at hgq; simp at hgq
    · exact h
  have hcont : Continuous (fun y => a * M.Fbar y) := continuous_const.mul (Fbar_cont M)
  have hR : a * M.Fbar q ≤ b := by
    have ht : Tendsto (fun y => a * M.Fbar y) (𝓝[>] q) (𝓝 (a * M.Fbar q)) :=
      (hcont.tendsto q).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : q < y := hy
    have h1 := hmax y (by linarith)
    have h2 := mul_le_mul_of_nonneg_left (S_inc_ge M hy'.le) ha.le
    have h3 : (y - q) * (a * M.Fbar y) ≤ (y - q) * b := by nlinarith
    exact le_of_mul_le_mul_left h3 (by linarith)
  have hL : b ≤ a * M.Fbar q := by
    have ht : Tendsto (fun y => a * M.Fbar y) (𝓝[<] q) (𝓝 (a * M.Fbar q)) :=
      (hcont.tendsto q).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT hq0] with y hy
    have h1 := hmax y hy.1.le
    have h2 := mul_le_mul_of_nonneg_left (S_inc_le M hy.2.le) ha.le
    have h3 : (q - y) * b ≤ (q - y) * (a * M.Fbar y) := by nlinarith
    exact le_of_mul_le_mul_left h3 (by linarith [hy.2])
  have heq : a * M.Fbar q = b := le_antisymm hR hL
  refine ⟨⟨hq0, ?_⟩, heq⟩
  by_contra hZ
  rw [Fbar_eq_zero M (not_lt.mp hZ)] at heq
  linarith


lemma Fbar_pos {x : ℝ} (hx : M.InSupport x) : 0 < M.Fbar x := by
  obtain ⟨z1, hxz, hz1⟩ := EReal.lt_iff_exists_real_btwn.mp hx.2
  have hxz' : x < z1 := by exact_mod_cast hxz
  have h := Fbar_strict M hx ⟨lt_trans hx.1 hxz', hz1⟩ hxz'
  linarith [Fbar_nonneg M z1]

lemma S_mono {x y : ℝ} (h : x ≤ y) : M.S x ≤ M.S y := by
  have := S_inc_ge M h
  nlinarith [Fbar_nonneg M y]

lemma kz_mono {x y : ℝ} (hx : M.InSupport x) (hy : M.InSupport y) (h : x ≤ y) :
    M.k x * M.z x ≤ M.k y * M.z y := by
  have hFx := Fbar_pos M hx
  have hFy := Fbar_pos M hy
  have hk : M.k x ≤ M.k y := by
    unfold Model.k
    rw [div_le_div_iff₀ hFx hFy]
    have h1 := S_mono M h
    have h2 := Fbar_anti M h
    have h3 := S_nonneg M hx.1.le
    nlinarith
  have hz : M.z x ≤ M.z y := by
    have hmem : ∀ t, M.InSupport t → t ∈ {x : ℝ | 0 ≤ x ∧ (x : EReal) < M.Z} :=
      fun t ht => ⟨ht.1.le, ht.2⟩
    exact M.strict_ifr.monotoneOn (hmem x hx) (hmem y hy) h
  have hz0 : 0 ≤ M.z x := div_nonneg (M.f_nonneg x) hFx.le
  have hk0 : 0 ≤ M.k y := div_nonneg (S_nonneg M hy.1.le) hFy.le
  exact mul_le_mul hk hz hz0 hk0

noncomputable def T (ws C0 ηr q : ℝ) : ℝ := (Real.log (ws * M.Fbar q) - Real.log C0) / ηr

noncomputable def Φ (ws C0 ηr lr q : ℝ) : ℝ := (2 - Real.exp (-(lr * T M ws C0 ηr q))) * M.S q

lemma T_eq {ws C0 ηr τ q : ℝ} (hC0 : 0 < C0) (hη : 0 < ηr)
    (h : ws * M.Fbar q = C0 * Real.exp (ηr * τ)) : T M ws C0 ηr q = τ := by
  unfold T
  rw [h, Real.log_mul hC0.ne' (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

lemma phi_deriv {ws C0 ηr lr x : ℝ} (hws : 0 < ws) (hη : 0 < ηr) (hx : M.InSupport x) :
    HasDerivAt (Φ M ws C0 ηr lr)
      ((M.Fbar x * Real.exp (-(lr * T M ws C0 ηr x)) / ηr) *
        (2 * ηr * Real.exp (lr * T M ws C0 ηr x) - ηr - lr * M.k x * M.z x)) x := by
  have hF := Fbar_pos M hx
  have h1 : HasDerivAt (fun q => ws * M.Fbar q) (ws * -M.f x) x :=
    (Fbar_hasDerivAt M hx).const_mul ws
  have h2 : HasDerivAt (fun q => Real.log (ws * M.Fbar q)) ((ws * -M.f x) / (ws * M.Fbar x)) x :=
    h1.log (by positivity)
  have h3 : HasDerivAt (fun q => (Real.log (ws * M.Fbar q) - Real.log C0) / ηr)
      (((ws * -M.f x) / (ws * M.Fbar x)) / ηr) x := (h2.sub_const _).div_const ηr
  have h4 := ((h3.const_mul lr).neg).exp
  have h5 := ((hasDerivAt_const x (2:ℝ)).sub h4).mul (S_hasDerivAt M x)
  have hΦ : Φ M ws C0 ηr lr = fun q =>
      (2 - Real.exp (-(lr * ((Real.log (ws * M.Fbar q) - Real.log C0) / ηr)))) * M.S q := rfl
  rw [hΦ]
  refine h5.congr_deriv ?_
  have hT : T M ws C0 ηr x = (Real.log (ws * M.Fbar x) - Real.log C0) / ηr := rfl
  simp only [Pi.neg_apply, Pi.sub_apply]
  rw [← hT]
  set E := Real.exp (-(lr * T M ws C0 ηr x))
  set G := Real.exp (lr * T M ws C0 ηr x)
  have hEG : E * G = 1 := by
    simp only [E, G]; rw [← Real.exp_add]; simp
  unfold Model.k Model.z
  have hFne : M.Fbar x ≠ 0 := hF.ne'
  have hη' : ηr ≠ 0 := hη.ne'
  have hws' : ws ≠ 0 := hws.ne'
  have e1 : (M.Fbar x * E / ηr) *
      (2 * ηr * G - ηr - lr * (M.S x / M.Fbar x) * (M.f x / M.Fbar x)) =
      2 * M.Fbar x * (E * G) - M.Fbar x * E - E * lr * M.S x * M.f x / (ηr * M.Fbar x) := by
    field_simp
  rw [e1, hEG]
  field_simp
  ring

lemma mono_core {ws C0 ηr lr τ0 q0 : ℝ} (hws : 0 < ws) (hC0 : 0 < C0) (hη : 0 < ηr)
    (hlr : 0 ≤ lr) (hq0 : M.InSupport q0)
    (hfoc : lr * M.k q0 * M.z q0 + ηr = 2 * ηr * Real.exp (lr * τ0))
    (hbr : ws * M.Fbar q0 = C0 * Real.exp (ηr * τ0)) {τ1 τ2 q1 q2 : ℝ}
    (hq1 : M.InSupport q1) (hq2 : M.InSupport q2)
    (h1 : ws * M.Fbar q1 = C0 * Real.exp (ηr * τ1))
    (h2 : ws * M.Fbar q2 = C0 * Real.exp (ηr * τ2)) :
    (τ1 ≤ τ2 → τ2 ≤ τ0 →
      (2 - Real.exp (-(lr * τ1))) * M.S q1 ≤ (2 - Real.exp (-(lr * τ2))) * M.S q2) ∧
    (τ0 ≤ τ1 → τ1 ≤ τ2 →
      (2 - Real.exp (-(lr * τ2))) * M.S q2 ≤ (2 - Real.exp (-(lr * τ1))) * M.S q1) := by
  -- order of quantities
  have ord : ∀ {a b ta tb : ℝ}, M.InSupport a → M.InSupport b →
      ws * M.Fbar a = C0 * Real.exp (ηr * ta) → ws * M.Fbar b = C0 * Real.exp (ηr * tb) →
      ta ≤ tb → b ≤ a := by
    intro a b ta tb ha hb hA hB ht
    by_contra hlt; push_neg at hlt
    have h3 := Fbar_strict M ha hb hlt
    have h4 : ws * M.Fbar b < ws * M.Fbar a := mul_lt_mul_of_pos_left h3 hws
    rw [hA, hB] at h4
    have h5 : Real.exp (ηr * tb) < Real.exp (ηr * ta) := lt_of_mul_lt_mul_left h4 hC0.le
    rw [Real.exp_lt_exp] at h5
    nlinarith
  have hsupp : ∀ {a b : ℝ}, M.InSupport a → M.InSupport b → ∀ x ∈ Set.Icc a b, M.InSupport x :=
    fun ha hb x hx => ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt (by exact_mod_cast hx.2) hb.2⟩
  have hT0 := T_eq M hC0 hη hbr
  have hT1 := T_eq M hC0 hη h1
  have hT2 := T_eq M hC0 hη h2
  have hΦ1 : Φ M ws C0 ηr lr q1 = (2 - Real.exp (-(lr * τ1))) * M.S q1 := by
    unfold Φ; rw [hT1]
  have hΦ2 : Φ M ws C0 ηr lr q2 = (2 - Real.exp (-(lr * τ2))) * M.S q2 := by
    unfold Φ; rw [hT2]
  have hcont : ∀ {a b : ℝ}, M.InSupport a → M.InSupport b →
      ContinuousOn (Φ M ws C0 ηr lr) (Set.Icc a b) := fun ha hb x hx =>
    (phi_deriv M (lr := lr) (C0 := C0) hws hη (hsupp ha hb x hx)).continuousAt.continuousWithinAt
  -- T is antitone on the support
  have hTle : ∀ {a b : ℝ}, M.InSupport a → M.InSupport b → a ≤ b →
      T M ws C0 ηr b ≤ T M ws C0 ηr a := by
    intro a b ha hb hab
    unfold T
    apply div_le_div_of_nonneg_right _ hη.le
    have := Real.log_le_log (mul_pos hws (Fbar_pos M hb))
      (mul_le_mul_of_nonneg_left (Fbar_anti M hab) hws.le)
    linarith
  have hfac : ∀ x, 0 ≤ M.Fbar x * Real.exp (-(lr * T M ws C0 ηr x)) / ηr := fun x =>
    div_nonneg (mul_nonneg (Fbar_nonneg M x) (Real.exp_pos _).le) hη.le
  refine ⟨fun ht12 ht20 => ?_, fun ht01 ht12 => ?_⟩
  · have hq21 : q2 ≤ q1 := ord hq1 hq2 h1 h2 ht12
    have hq02 : q0 ≤ q2 := ord hq2 hq0 h2 hbr ht20
    have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc q2 q1) (hcont hq2 hq1)
      (fun x hx => (phi_deriv M (lr := lr) (C0 := C0) hws hη
        (hsupp hq2 hq1 x (interior_subset hx))).hasDerivWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        have hxs : M.InSupport x := hsupp hq2 hq1 x ⟨hx.1.le, hx.2.le⟩
        have hTx : T M ws C0 ηr x ≤ τ0 := hT0 ▸ hTle hq0 hxs (le_trans hq02 hx.1.le)
        have he : Real.exp (lr * T M ws C0 ηr x) ≤ Real.exp (lr * τ0) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hTx hlr)
        have hkz := kz_mono M hq0 hxs (le_trans hq02 hx.1.le)
        have hkz' : lr * (M.k q0 * M.z q0) ≤ lr * (M.k x * M.z x) :=
          mul_le_mul_of_nonneg_left hkz hlr
        apply mul_nonpos_of_nonneg_of_nonpos (hfac x)
        nlinarith)
    rw [← hΦ1, ← hΦ2]
    exact hanti ⟨le_rfl, hq21⟩ ⟨hq21, le_rfl⟩ hq21
  · have hq21 : q2 ≤ q1 := ord hq1 hq2 h1 h2 ht12
    have hq10 : q1 ≤ q0 := ord hq0 hq1 hbr h1 ht01
    have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc q2 q1) (hcont hq2 hq1)
      (fun x hx => (phi_deriv M (lr := lr) (C0 := C0) hws hη
        (hsupp hq2 hq1 x (interior_subset hx))).hasDerivWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        have hxs : M.InSupport x := hsupp hq2 hq1 x ⟨hx.1.le, hx.2.le⟩
        have hTx : τ0 ≤ T M ws C0 ηr x := hT0 ▸ hTle hxs hq0 (le_trans hx.2.le hq10)
        have he : Real.exp (lr * τ0) ≤ Real.exp (lr * T M ws C0 ηr x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hTx hlr)
        have hkz := kz_mono M hxs hq0 (le_trans hx.2.le hq10)
        have hkz' : lr * (M.k x * M.z x) ≤ lr * (M.k q0 * M.z q0) :=
          mul_le_mul_of_nonneg_left hkz hlr
        apply mul_nonneg (hfac x)
        nlinarith)
    rw [← hΦ1, ← hΦ2]
    exact hmono ⟨le_rfl, hq21⟩ ⟨hq21, le_rfl⟩ hq21


lemma eq_facts {Λ0 Cs Cr ws qs : ℝ} (hK : 0 < 1 - M.ρ Cs) (hR : 0 < 1 - M.ρ Cr) (hΛ0 : 0 < Λ0)
    (hfeas : M.c * Real.exp (M.η Cs * M.t1) < M.p * Λ0 * Real.exp (-(M.lamS * M.t1)))
    (heq : M.IsEquilibrium Λ0 Cs Cr ws qs) :
    0 < M.retailerProfit Cr ws qs ∧ 0 < ws ∧ ws < M.p := by
  have hπ := (core M hK hR hΛ0 hfeas heq).1
  obtain ⟨hws, ⟨hqs, hBR⟩, hopt⟩ := heq
  have he1 : 0 < Real.exp (-(M.lamS * M.t1)) := Real.exp_pos _
  have hb : 0 < M.c * Real.exp (M.η Cs * M.t1) := mul_pos M.c_pos (Real.exp_pos _)
  have hΛe : 0 < Λ0 * Real.exp (-(M.lamS * M.t1)) := mul_pos hΛ0 he1
  have hb' : M.c * Real.exp (M.η Cs * M.t1) / (Λ0 * Real.exp (-(M.lamS * M.t1))) < M.p := by
    rw [div_lt_iff₀ hΛe]; linarith
  have hd := div_pos hb hΛe
  obtain ⟨w', hw'⟩ : ∃ w', w' = (M.c * Real.exp (M.η Cs * M.t1) /
      (Λ0 * Real.exp (-(M.lamS * M.t1))) + M.p) / 2 := ⟨_, rfl⟩
  have hw'0 : 0 ≤ w' := by rw [hw']; linarith
  have hw'p : w' < M.p := by rw [hw']; linarith
  obtain ⟨q', hq', hmax'⟩ := exists_max M (a := Λ0 * Real.exp (-(M.lamS * M.t1)) * w')
    (mul_nonneg hΛe.le hw'0) hb
  have ha' : M.c * Real.exp (M.η Cs * M.t1) < Λ0 * Real.exp (-(M.lamS * M.t1)) * w' := by
    have h2 : M.c * Real.exp (M.η Cs * M.t1) / (Λ0 * Real.exp (-(M.lamS * M.t1))) < w' := by
      rw [hw']; linarith
    rw [div_lt_iff₀ hΛe] at h2; linarith
  obtain ⟨q0, hq0, hpos0⟩ := exists_pos M hb ha'
  have hg' := lt_of_lt_of_le hpos0 (hmax' q0 hq0)
  have hSq' : 0 < M.S q' := by
    by_contra hcon; replace hcon := not_lt.mp hcon
    have : Λ0 * Real.exp (-(M.lamS * M.t1)) * w' * M.S q' ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hΛe.le hw'0) hcon
    nlinarith
  have hBR' : M.IsBestResponse Λ0 Cs w' q' := ⟨hq', fun q'' hq'' => by
    rw [prof_eq, prof_eq]; exact mul_le_mul_of_nonneg_left (hmax' q'' hq'') hK.le⟩
  have hRet := hopt w' q' hw'0 hBR'
  have hRpos : 0 < M.retailerProfit Cr w' q' := by
    unfold Model.retailerProfit
    have : 0 < M.p - w' := by linarith
    positivity
  have hRs : 0 < M.retailerProfit Cr ws qs := lt_of_lt_of_le hRpos hRet
  have hS := S_nonneg M hqs
  refine ⟨hRs, ?_, ?_⟩
  · by_contra h; push_neg at h
    rw [prof_eq] at hπ
    have h1 : Λ0 * Real.exp (-(M.lamS * M.t1)) * ws * M.S qs ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hΛe.le h) hS
    have h2 : 0 ≤ M.c * Real.exp (M.η Cs * M.t1) * qs := mul_nonneg hb.le hqs
    have h3 : Λ0 * Real.exp (-(M.lamS * M.t1)) * ws * M.S qs -
        M.c * Real.exp (M.η Cs * M.t1) * qs ≤ 0 := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos hK.le h3
    linarith
  · by_contra h; push_neg at h
    have : M.retailerProfit Cr ws qs ≤ 0 := by
      unfold Model.retailerProfit
      have h1 : 0 ≤ Real.exp (-(M.lamS * M.t1)) * (1 - M.ρ Cr) := mul_nonneg he1.le hR.le
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos h1 (by linarith)) hS
    linarith

lemma ab_rel (Cs Cr τ : ℝ) : M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * M.cR Cs Cr τ =
    M.c * Real.exp (M.η Cs * M.t1) := by
  unfold Model.ΛR Model.cR
  have : Real.exp (-(M.η Cr * (M.t2 + τ))) * Real.exp (-(M.lamS * M.t1)) *
      (M.c * Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * (M.t2 + τ))) =
      M.c * (Real.exp (-(M.η Cr * (M.t2 + τ))) * Real.exp (-(M.lamS * M.t1)) *
        Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * (M.t2 + τ))) := by ring
  rw [this, ← Real.exp_add, ← Real.exp_add]
  congr 2; ring

lemma cR_eq (Cs Cr τ : ℝ) : M.cR Cs Cr τ =
    (M.c * Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * M.t2)) * Real.exp (M.η Cr * τ) := by
  unfold Model.cR
  rw [mul_assoc, ← Real.exp_add]
  congr 2; ring

lemma ΛRK_pos (Cr τ : ℝ) : 0 < M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) := by
  unfold Model.ΛR; positivity

lemma br_foc {Cs Cr ws τ q : ℝ} (hK : 0 < 1 - M.ρ Cs)
    (hbr : M.IsBestResponse (M.ΛR Cr τ) Cs ws q) (hlt : M.cR Cs Cr τ < ws) :
    M.InSupport q ∧ ws * M.Fbar q = M.cR Cs Cr τ := by
  have hL := ΛRK_pos M Cr τ
  have hrel := ab_rel M Cs Cr τ
  have hb : 0 < M.c * Real.exp (M.η Cs * M.t1) := mul_pos M.c_pos (Real.exp_pos _)
  have hab : M.c * Real.exp (M.η Cs * M.t1) < M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * ws := by
    rw [← hrel]; exact mul_lt_mul_of_pos_left hlt hL
  have hmax : ∀ q', 0 ≤ q' →
      M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * ws * M.S q' - M.c * Real.exp (M.η Cs * M.t1) * q' ≤
      M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * ws * M.S q - M.c * Real.exp (M.η Cs * M.t1) * q :=
    fun q' hq' => by
      have := hbr.2 q' hq'
      rw [prof_eq, prof_eq] at this
      exact le_of_mul_le_mul_left this hK
  obtain ⟨hs, he⟩ := focn M hb hab hbr.1 hmax
  refine ⟨hs, ?_⟩
  have : M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * (ws * M.Fbar q) =
      M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * M.cR Cs Cr τ := by
    rw [hrel, ← he]; ring
  exact mul_left_cancel₀ hL.ne' this

lemma Xi_mem {s x : ℝ} (hs : 0 ≤ s) : 0 ≤ Xi s x ∧ Xi s x ≤ s :=
  ⟨le_max_left _ _, max_le hs (min_le_left _ _)⟩

lemma Xi_a {s x : ℝ} (h : x < Xi s x) : Xi s x = 0 := by
  simp only [Xi, max_def, min_def] at h ⊢
  split_ifs at h ⊢ <;> linarith

lemma Xi_b {s x : ℝ} (hs : 0 ≤ s) (h : Xi s x < x) : Xi s x = s := by
  simp only [Xi, max_def, min_def] at h ⊢
  split_ifs at h ⊢ <;> linarith

lemma gen {Cs Cr Λ0 ws qs τs τ0 q0 : ℝ} (hCr : Cr ∈ Set.Ioo M.Cmin M.Cmax)
    (hK : 0 < 1 - M.ρ Cs) (hR : 0 < 1 - M.ρ Cr) (hΛ0 : 0 < Λ0)
    (hfeas : M.c * Real.exp (M.η Cs * M.t1) < M.p * Λ0 * Real.exp (-(M.lamS * M.t1)))
    (heq : M.IsEquilibrium Λ0 Cs Cr ws qs) (hτs : 0 ≤ τs)
    (hiff : ∀ τ : ℝ, 0 ≤ τ → (Λ0 ≤ M.ΛR Cr τ ↔ τ ≤ τs)) (hΛ0R : Λ0 ≤ M.ΛR Cr 0)
    (hq0 : M.InSupport q0)
    (hfoc : M.lamR * M.k q0 * M.z q0 + M.η Cr = 2 * M.η Cr * Real.exp (M.lamR * τ0))
    (hbr : ws * M.Fbar q0 = M.cR Cs Cr τ0) :
    ∃ q : ℝ, M.IsOptimalExtension Cs Cr ws (M.supplierProfit Λ0 Cs ws qs) (Xi τs τ0) q ∧
      M.retailerProfit Cr ws qs ≤ M.retailerProfitR Cr (Xi τs τ0) ws q := by
  obtain ⟨hπ, hcore⟩ := core M hK hR hΛ0 hfeas heq
  obtain ⟨hRet, hws, hwp⟩ := eq_facts M hK hR hΛ0 hfeas heq
  have hηr := M.η_pos Cr hCr
  have hfeasτ : ∀ τ, 0 ≤ τ → τ ≤ τs →
      ∃ q, M.FeasibleExtension Cs Cr ws (M.supplierProfit Λ0 Cs ws qs) τ q := by
    intro τ h0 h1
    obtain ⟨q, hq, hle⟩ := (hcore (M.ΛR Cr τ)).mpr ((hiff τ h0).mpr h1)
    exact ⟨q, h0, hq, hle⟩
  have hfoc' : ∀ τ q, M.FeasibleExtension Cs Cr ws (M.supplierProfit Λ0 Cs ws qs) τ q →
      M.InSupport q ∧ ws * M.Fbar q = M.cR Cs Cr τ := by
    rintro τ q ⟨h0, hbrq, hle⟩
    have hlt : M.cR Cs Cr τ < ws := by
      by_contra hc; push_neg at hc
      have hnp : M.supplierProfit (M.ΛR Cr τ) Cs ws q ≤ 0 := by
        rw [prof_eq]
        apply mul_nonpos_of_nonneg_of_nonpos hK.le
        have hL := ΛRK_pos M Cr τ
        have hab : M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * ws ≤
            M.c * Real.exp (M.η Cs * M.t1) := by
          rw [← ab_rel M Cs Cr τ]; exact mul_le_mul_of_nonneg_left hc hL.le
        rcases hbrq.1.eq_or_lt with h | h
        · rw [← h, S_zero]; simp
        · exact (neg_of_le M (mul_nonneg hL.le hws.le) hab
            (mul_pos M.c_pos (Real.exp_pos _)) h).le
      linarith
    exact br_foc M hK hbrq hlt
  obtain ⟨hX0, hXs⟩ := Xi_mem (x := τ0) hτs
  obtain ⟨qst, hqst⟩ := hfeasτ _ hX0 hXs
  obtain ⟨hqsts, hqstF⟩ := hfoc' _ _ hqst
  have hC0 : 0 < M.c * Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * M.t2) :=
    mul_pos M.c_pos (Real.exp_pos _)
  have hmono : ∀ τ1 τ2 q1 q2 : ℝ, M.InSupport q1 → M.InSupport q2 →
      ws * M.Fbar q1 = M.cR Cs Cr τ1 → ws * M.Fbar q2 = M.cR Cs Cr τ2 →
      (τ1 ≤ τ2 → τ2 ≤ τ0 →
        (2 - Real.exp (-(M.lamR * τ1))) * M.S q1 ≤ (2 - Real.exp (-(M.lamR * τ2))) * M.S q2) ∧
      (τ0 ≤ τ1 → τ1 ≤ τ2 →
        (2 - Real.exp (-(M.lamR * τ2))) * M.S q2 ≤ (2 - Real.exp (-(M.lamR * τ1))) * M.S q1) := by
    intro τ1 τ2 q1 q2 hq1 hq2 h1 h2
    exact mono_core M hws hC0 hηr M.lamR_nonneg hq0 hfoc (by rw [hbr, cR_eq]) hq1 hq2
      (by rw [h1, cR_eq]) (by rw [h2, cR_eq])
  have hRR : ∀ τ q, M.retailerProfitR Cr τ ws q =
      (Real.exp (-(M.lamS * M.t1)) * (1 - M.ρ Cr) * (M.p - ws)) *
        ((2 - Real.exp (-(M.lamR * τ))) * M.S q) := by
    intro τ q; unfold Model.retailerProfitR; ring
  have hcoef : 0 ≤ Real.exp (-(M.lamS * M.t1)) * (1 - M.ρ Cr) * (M.p - ws) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hR.le) (by linarith)
  have hopt : ∀ τ' q', M.FeasibleExtension Cs Cr ws (M.supplierProfit Λ0 Cs ws qs) τ' q' →
      M.retailerProfitR Cr τ' ws q' ≤ M.retailerProfitR Cr (Xi τs τ0) ws qst := by
    intro τ' q' hf
    obtain ⟨hs', hF'⟩ := hfoc' _ _ hf
    have hτ'0 : 0 ≤ τ' := hf.1
    have hτ's : τ' ≤ τs := (hiff τ' hτ'0).mp ((hcore _).mp ⟨q', hf.2.1, hf.2.2⟩)
    rw [hRR, hRR]
    apply mul_le_mul_of_nonneg_left _ hcoef
    have hm := hmono _ _ _ _ hs' hqsts hF' hqstF
    have hm2 := hmono _ _ _ _ hqsts hs' hqstF hF'
    by_cases hA : τ' ≤ Xi τs τ0 ∧ Xi τs τ0 ≤ τ0
    · exact hm.1 hA.1 hA.2
    · have hB : Xi τs τ0 ≤ τ' ∧ τ0 ≤ Xi τs τ0 := by
        rcases le_or_gt (Xi τs τ0) τ0 with h1 | h1
        · have h2 : Xi τs τ0 < τ' := by
            by_contra h; exact hA ⟨not_lt.mp h, h1⟩
          rcases h1.lt_or_eq with h3 | h3
          · exfalso; have := Xi_b hτs h3; linarith
          · exact ⟨h2.le, h3.ge⟩
        · exact ⟨by rw [Xi_a h1]; exact hτ'0, h1.le⟩
      exact hm2.2 hB.2 hB.1
  refine ⟨qst, ⟨hqst, hopt⟩, ?_⟩
  have hR0 : ∀ q, M.retailerProfitR Cr 0 ws q = M.retailerProfit Cr ws q := by
    intro q; unfold Model.retailerProfitR Model.retailerProfit
    rw [mul_zero, neg_zero, Real.exp_zero]; ring
  rcases hΛ0R.lt_or_eq with hlt | heqΛ
  · obtain ⟨q0', hf0⟩ := hfeasτ 0 le_rfl hτs
    have h1 := heq.2.1.2 q0' hf0.2.1.1
    have h2 := hf0.2.1.2 qs heq.2.1.1
    unfold Model.supplierProfit at h1 h2
    have h3 : 0 ≤ ((1 - M.ρ Cs) * (M.ΛR Cr 0 - Λ0) * Real.exp (-(M.lamS * M.t1)) * ws) *
        (M.S q0' - M.S qs) := by linarith
    have hpos : 0 < (1 - M.ρ Cs) * (M.ΛR Cr 0 - Λ0) * Real.exp (-(M.lamS * M.t1)) * ws :=
      mul_pos (mul_pos (mul_pos hK (by linarith)) (Real.exp_pos _)) hws
    have hS : M.S qs ≤ M.S q0' := by
      have := (mul_nonneg_iff_of_pos_left hpos).mp h3; linarith
    calc M.retailerProfit Cr ws qs ≤ M.retailerProfit Cr ws q0' := by
          unfold Model.retailerProfit
          exact mul_le_mul_of_nonneg_left hS hcoef
      _ = M.retailerProfitR Cr 0 ws q0' := (hR0 q0').symm
      _ ≤ _ := hopt 0 q0' hf0
  · have hf0 : M.FeasibleExtension Cs Cr ws (M.supplierProfit Λ0 Cs ws qs) 0 qs :=
      ⟨le_rfl, heqΛ ▸ heq.2.1, by rw [heqΛ]⟩
    calc M.retailerProfit Cr ws qs = M.retailerProfitR Cr 0 ws qs := (hR0 qs).symm
      _ ≤ _ := hopt 0 qs hf0

end P874

open SupplyChainFactoring.Extension in
theorem solution (M : Model) {Cs Cr CN CF C1 CRmax : ℝ}
    (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) (hCr : Cr ∈ Set.Ioo M.Cmin M.Cmax)
    (hCN : M.IsThresholdN Cr CN) (hCF : M.IsThresholdF Cr CF) (hC1 : M.IsThreshold1 Cr C1)
    (hCRmax : M.IsThresholdRmax Cr CRmax) :
    -- (i)
    (CRmax ≤ Cs → ∀ τ w qR qF : ℝ, 0 ≤ τ →
      M.IsBestResponse (M.ΛR Cr τ) Cs w qR → M.IsBestResponse (M.ΛF Cs Cr) Cs w qF →
      M.supplierProfit (M.ΛR Cr τ) Cs w qR ≤ M.supplierProfit (M.ΛF Cs Cr) Cs w qF) ∧
    -- (ii)
    (CN < Cs → Cs < CRmax →
      -- first case: ℂ_𝓝 < Cs ≤ ℂ_1, existing non-recourse equilibrium
      (Cs ≤ C1 → ∀ ws qs τ0 q0 : ℝ, M.IsEquilibrium (M.ΛN Cr) Cs Cr ws qs →
        M.InSupport q0 →
        M.lamR * M.k q0 * M.z q0 + M.η Cr = 2 * M.η Cr * Real.exp (M.lamR * τ0) →
        ws * M.Fbar q0 = M.cR Cs Cr τ0 →
        ∃ q : ℝ,
          M.IsOptimalExtension Cs Cr ws (M.supplierProfit (M.ΛN Cr) Cs ws qs)
            (Xi (-Real.log (1 - M.ρ Cr) / M.η Cr) τ0) q ∧
          M.retailerProfit Cr ws qs ≤
            M.retailerProfitR Cr (Xi (-Real.log (1 - M.ρ Cr) / M.η Cr) τ0) ws q) ∧
      -- second case: ℂ_𝓕 ∨ ℂ_1 < Cs < ℂ^max_𝓡, existing recourse equilibrium
      (max CF C1 < Cs → ∀ ws qs τ0 q0 : ℝ, M.IsEquilibrium (M.ΛF Cs Cr) Cs Cr ws qs →
        M.InSupport q0 →
        M.lamR * M.k q0 * M.z q0 + M.η Cr = 2 * M.η Cr * Real.exp (M.lamR * τ0) →
        ws * M.Fbar q0 = M.cR Cs Cr τ0 →
        ∃ q : ℝ,
          M.IsOptimalExtension Cs Cr ws (M.supplierProfit (M.ΛF Cs Cr) Cs ws qs)
            (Xi (-Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2) τ0) q ∧
          M.retailerProfit Cr ws qs ≤
            M.retailerProfitR Cr (Xi (-Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2) τ0) ws q)) := by
  have hηr := M.η_pos Cr hCr
  have hc := M.c_pos
  have hcp := M.c_lt_p
  have hK := P874.one_sub_rho_pos M hCs
  refine ⟨?_, ?_⟩
  · intro hle τ w qR qF hτ hR hF
    have hΛ : M.ΛR Cr τ ≤ M.ΛF Cs Cr := by
      have h1 : M.ΛF CRmax Cr ≤ M.ΛF Cs Cr := by
        rcases hle.lt_or_eq with h | h
        · exact (P874.ΛF_lt M hCRmax.1 hCs h).le
        · rw [h]
      rw [hCRmax.2.1] at h1
      refine le_trans ?_ h1
      unfold Model.ΛR
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hS := P874.S_nonneg M hR.1
    rcases le_or_gt 0 w with hw | hw
    · calc M.supplierProfit (M.ΛR Cr τ) Cs w qR ≤ M.supplierProfit (M.ΛF Cs Cr) Cs w qR := by
            rw [P874.prof_eq, P874.prof_eq]
            apply mul_le_mul_of_nonneg_left _ hK.le
            have h1 := mul_le_mul_of_nonneg_right hΛ
              (mul_nonneg (mul_nonneg (Real.exp_pos (-(M.lamS * M.t1))).le hw) hS)
            nlinarith
        _ ≤ M.supplierProfit (M.ΛF Cs Cr) Cs w qF := hF.2 qR hR.1
    · have hΛR : 0 < M.ΛR Cr τ := by unfold Model.ΛR; positivity
      have h1 : M.supplierProfit (M.ΛR Cr τ) Cs w qR ≤ 0 := by
        rw [P874.prof_eq]
        apply mul_nonpos_of_nonneg_of_nonpos hK.le
        have h2 : M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * w * M.S qR ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (mul_pos hΛR (Real.exp_pos _)).le hw.le) hS
        have h3 : 0 ≤ M.c * Real.exp (M.η Cs * M.t1) * qR :=
          mul_nonneg (mul_pos hc (Real.exp_pos _)).le hR.1
        linarith
      have h2 : 0 ≤ M.supplierProfit (M.ΛF Cs Cr) Cs w qF := by
        have := hF.2 0 le_rfl
        rw [P874.prof_eq, P874.S_zero] at this
        simp at this
        linarith
      linarith
  · intro hCNs hCsR
    refine ⟨fun _ ws qs τ0 q0 heq hq0 hfoc hbr => ?_,
      fun hmx ws qs τ0 q0 heq hq0 hfoc hbr => ?_⟩
    · have hRpos : 0 < 1 - M.ρ Cr := by
        have hpos : 0 < M.c * Real.exp ((M.η CN + M.lamS) * M.t1 + M.η Cr * M.t2) :=
          mul_pos hc (Real.exp_pos _)
        rw [hCN.2.1] at hpos
        exact pos_of_mul_pos_right hpos (by linarith)
      have hlt : M.c * Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * M.t2) <
          M.p * (1 - M.ρ Cr) := by
        have hη := M.η_antitone hCN.1 hCs hCNs.le
        have hle : M.c * Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * M.t2) ≤
            M.p * (1 - M.ρ Cr) := by
          rw [← hCN.2.1]
          apply mul_le_mul_of_nonneg_left _ hc.le
          apply Real.exp_le_exp.mpr
          nlinarith [M.t1_pos]
        refine lt_of_le_of_ne hle (fun h => ?_)
        have := hCN.2.2 Cs hCs h
        linarith
      have hfeas : M.c * Real.exp (M.η Cs * M.t1) <
          M.p * M.ΛN Cr * Real.exp (-(M.lamS * M.t1)) := by
        unfold Model.ΛN
        rw [show (M.η Cs + M.lamS) * M.t1 + M.η Cr * M.t2 =
          M.η Cs * M.t1 + (M.lamS * M.t1 + M.η Cr * M.t2) by ring, Real.exp_add] at hlt
        have hE : Real.exp (M.lamS * M.t1 + M.η Cr * M.t2) *
            (Real.exp (-(M.η Cr * M.t2)) * Real.exp (-(M.lamS * M.t1))) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
        have hEpos : 0 < Real.exp (-(M.η Cr * M.t2)) * Real.exp (-(M.lamS * M.t1)) := by
          positivity
        have h1 := mul_lt_mul_of_pos_right hlt hEpos
        have h2 : M.c * (Real.exp (M.η Cs * M.t1) * Real.exp (M.lamS * M.t1 + M.η Cr * M.t2)) *
            (Real.exp (-(M.η Cr * M.t2)) * Real.exp (-(M.lamS * M.t1))) =
            M.c * Real.exp (M.η Cs * M.t1) := by
          calc _ = M.c * Real.exp (M.η Cs * M.t1) * (Real.exp (M.lamS * M.t1 + M.η Cr * M.t2) *
            (Real.exp (-(M.η Cr * M.t2)) * Real.exp (-(M.lamS * M.t1)))) := by ring
            _ = _ := by rw [hE, mul_one]
        linarith
      have hΛNpos : 0 < M.ΛN Cr := mul_pos (Real.exp_pos _) hRpos
      have hτs : 0 ≤ -Real.log (1 - M.ρ Cr) / M.η Cr := by
        apply div_nonneg _ hηr.le
        have := Real.log_nonpos hRpos.le (by linarith [(M.ρ_mem Cr hCr).1])
        linarith
      have hiff : ∀ τ : ℝ, 0 ≤ τ →
          (M.ΛN Cr ≤ M.ΛR Cr τ ↔ τ ≤ -Real.log (1 - M.ρ Cr) / M.η Cr) := by
        intro τ _
        unfold Model.ΛN Model.ΛR
        rw [show -(M.η Cr * (M.t2 + τ)) = -(M.η Cr * M.t2) + -(M.η Cr * τ) by ring, Real.exp_add,
          mul_le_mul_iff_of_pos_left (Real.exp_pos _), ← Real.log_le_iff_le_exp hRpos,
          le_div_iff₀ hηr]
        constructor <;> intro h <;> linarith
      have hΛ0R : M.ΛN Cr ≤ M.ΛR Cr 0 := by
        unfold Model.ΛN Model.ΛR
        rw [add_zero]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (by linarith [(M.ρ_mem Cr hCr).1])
      exact P874.gen M hCr hK hRpos hΛNpos hfeas heq hτs hiff hΛ0R hq0 hfoc hbr
    · have hCFs : CF < Cs := lt_of_le_of_lt (le_max_left _ _) hmx
      have hΛlt := P874.ΛF_lt M (Cr := Cr) hCF.1 hCs hCFs
      have hle : M.c * Real.exp ((M.η Cs + M.lamS) * M.t1) ≤ M.p * M.ΛF CF Cr := by
        rw [← hCF.2.1]
        apply mul_le_mul_of_nonneg_left _ hc.le
        apply Real.exp_le_exp.mpr
        have := M.η_antitone hCF.1 hCs hCFs.le
        nlinarith [M.t1_pos]
      have hlt : M.c * Real.exp ((M.η Cs + M.lamS) * M.t1) < M.p * M.ΛF Cs Cr :=
        lt_of_le_of_lt hle (mul_lt_mul_of_pos_left hΛlt (by linarith))
      have hΛF : 0 < M.ΛF Cs Cr := by
        have : 0 < M.p * M.ΛF Cs Cr := lt_trans (mul_pos hc (Real.exp_pos _)) hlt
        exact pos_of_mul_pos_right this (by linarith)
      have hRpos : 0 < 1 - M.ρ Cr := by
        have h1 : 1 < Real.exp (M.η Cs * M.t2) :=
          Real.one_lt_exp_iff.mpr (mul_pos (M.η_pos Cs hCs) M.t2_pos)
        have h2 := (M.ρ_mem Cs hCs).1
        have h3 := hΛF
        unfold Model.ΛF at h3
        linarith
      have hfeas : M.c * Real.exp (M.η Cs * M.t1) <
          M.p * M.ΛF Cs Cr * Real.exp (-(M.lamS * M.t1)) := by
        rw [show (M.η Cs + M.lamS) * M.t1 = M.η Cs * M.t1 + M.lamS * M.t1 by ring,
          Real.exp_add] at hlt
        have hE : Real.exp (M.lamS * M.t1) * Real.exp (-(M.lamS * M.t1)) = 1 := by
          rw [← Real.exp_add]; simp
        have h1 := mul_lt_mul_of_pos_right hlt (Real.exp_pos (-(M.lamS * M.t1)))
        have h3 : M.c * (Real.exp (M.η Cs * M.t1) * Real.exp (M.lamS * M.t1)) *
            Real.exp (-(M.lamS * M.t1)) = M.c * Real.exp (M.η Cs * M.t1) := by
          calc _ = M.c * Real.exp (M.η Cs * M.t1) *
              (Real.exp (M.lamS * M.t1) * Real.exp (-(M.lamS * M.t1))) := by ring
            _ = _ := by rw [hE, mul_one]
        linarith
      have hmax : M.ΛF Cs Cr < Real.exp (-(M.η Cr * M.t2)) := by
        rw [← hCRmax.2.1]; exact P874.ΛF_lt M hCs hCRmax.1 hCsR
      have hτs : 0 ≤ -Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2 := by
        have := (Real.log_lt_iff_lt_exp hΛF).mpr hmax
        rw [sub_nonneg, le_div_iff₀ hηr]; linarith
      have hiff : ∀ τ : ℝ, 0 ≤ τ →
          (M.ΛF Cs Cr ≤ M.ΛR Cr τ ↔ τ ≤ -Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2) := by
        intro τ _
        unfold Model.ΛR
        rw [← Real.log_le_iff_le_exp hΛF, le_sub_iff_add_le, le_div_iff₀ hηr]
        constructor <;> intro h <;> linarith
      have hΛ0R : M.ΛF Cs Cr ≤ M.ΛR Cr 0 := by
        unfold Model.ΛR
        rw [add_zero]
        exact hmax.le
      exact P874.gen M hCr hK hRpos hΛF hfeas heq hτs hiff hΛ0R hq0 hfoc hbr
