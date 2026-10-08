-- Prove2me | solution 1 for SupplyChainFactoring.Extension.maximal_acceptable_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:22:11.325727+00:00
-- url     : https://prove2.me/submissions/445982fb-5ec3-4f5b-a9ec-035b1b868f23

import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

set_option autoImplicit false

namespace DA6EB6F3

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

end DA6EB6F3

open SupplyChainFactoring.Extension in
theorem solution (M : Model) {Cs Cr CN CF CRmax : ℝ}
    (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) (hCr : Cr ∈ Set.Ioo M.Cmin M.Cmax)
    (hCN : M.IsThresholdN Cr CN) (hCF : M.IsThresholdF Cr CF)
    (hCRmax : M.IsThresholdRmax Cr CRmax) :
    (CN < Cs → ∀ ws qs : ℝ, M.IsEquilibrium (M.ΛN Cr) Cs Cr ws qs →
      0 ≤ -Real.log (1 - M.ρ Cr) / M.η Cr ∧
      ∀ τ : ℝ, 0 ≤ τ →
        ((∃ q : ℝ, M.FeasibleExtension Cs Cr ws (M.supplierProfit (M.ΛN Cr) Cs ws qs) τ q) ↔
          τ ≤ -Real.log (1 - M.ρ Cr) / M.η Cr)) ∧
    (CF < Cs → Cs < CRmax → ∀ ws qs : ℝ, M.IsEquilibrium (M.ΛF Cs Cr) Cs Cr ws qs →
      0 < -Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2 ∧
      ∀ τ : ℝ, 0 ≤ τ →
        ((∃ q : ℝ, M.FeasibleExtension Cs Cr ws (M.supplierProfit (M.ΛF Cs Cr) Cs ws qs) τ q) ↔
          τ ≤ -Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2)) := by
  have hηr := M.η_pos Cr hCr
  have hc := M.c_pos
  have hcp := M.c_lt_p
  have hK := DA6EB6F3.one_sub_rho_pos M hCs
  have hFE : ∀ (Λ0 ws qs τ : ℝ), 0 ≤ τ →
      ((∃ q : ℝ, M.FeasibleExtension Cs Cr ws (M.supplierProfit Λ0 Cs ws qs) τ q) ↔
      (∃ q, M.IsBestResponse (M.ΛR Cr τ) Cs ws q ∧
        M.supplierProfit Λ0 Cs ws qs ≤ M.supplierProfit (M.ΛR Cr τ) Cs ws q)) := by
    intro Λ0 ws qs τ hτ
    unfold Model.FeasibleExtension
    simp only [hτ, true_and]
  refine ⟨?_, ?_⟩
  · intro hCNs ws qs heq
    have hRpos : 0 < 1 - M.ρ Cr := by
      have hpos : 0 < M.c * Real.exp ((M.η CN + M.lamS) * M.t1 + M.η Cr * M.t2) :=
        mul_pos hc (Real.exp_pos _)
      rw [hCN.2.1] at hpos
      exact pos_of_mul_pos_right hpos (by linarith)
    have hlt : M.c * Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * M.t2) < M.p * (1 - M.ρ Cr) := by
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
      have hEpos : 0 < Real.exp (-(M.η Cr * M.t2)) * Real.exp (-(M.lamS * M.t1)) := by positivity
      have h1 := mul_lt_mul_of_pos_right hlt hEpos
      have h2 : M.c * (Real.exp (M.η Cs * M.t1) * Real.exp (M.lamS * M.t1 + M.η Cr * M.t2)) *
          (Real.exp (-(M.η Cr * M.t2)) * Real.exp (-(M.lamS * M.t1))) =
          M.c * Real.exp (M.η Cs * M.t1) := by
        calc _ = M.c * Real.exp (M.η Cs * M.t1) * (Real.exp (M.lamS * M.t1 + M.η Cr * M.t2) *
          (Real.exp (-(M.η Cr * M.t2)) * Real.exp (-(M.lamS * M.t1)))) := by ring
          _ = _ := by rw [hE, mul_one]
      linarith
    have hΛNpos : 0 < M.ΛN Cr := mul_pos (Real.exp_pos _) hRpos
    obtain ⟨-, hiff⟩ := DA6EB6F3.core M hK hRpos hΛNpos hfeas heq
    refine ⟨?_, fun τ hτ => ?_⟩
    · apply div_nonneg _ hηr.le
      have := Real.log_nonpos hRpos.le (by linarith [(M.ρ_mem Cr hCr).1])
      linarith
    · rw [hFE _ _ _ _ hτ, hiff]
      unfold Model.ΛN Model.ΛR
      rw [show -(M.η Cr * (M.t2 + τ)) = -(M.η Cr * M.t2) + -(M.η Cr * τ) by ring, Real.exp_add,
        mul_le_mul_iff_of_pos_left (Real.exp_pos _), ← Real.log_le_iff_le_exp hRpos,
        le_div_iff₀ hηr]
      constructor <;> intro h <;> linarith
  · intro hCFs hCsR ws qs heq
    have hΛlt := DA6EB6F3.ΛF_lt M (Cr := Cr) hCF.1 hCs hCFs
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
    obtain ⟨-, hiff⟩ := DA6EB6F3.core M hK hRpos hΛF hfeas heq
    have hmax : M.ΛF Cs Cr < Real.exp (-(M.η Cr * M.t2)) := by
      rw [← hCRmax.2.1]; exact DA6EB6F3.ΛF_lt M hCs hCRmax.1 hCsR
    refine ⟨?_, fun τ hτ => ?_⟩
    · have := (Real.log_lt_iff_lt_exp hΛF).mpr hmax
      rw [sub_pos, lt_div_iff₀ hηr]; linarith
    · rw [hFE _ _ _ _ hτ, hiff]
      unfold Model.ΛR
      rw [← Real.log_le_iff_le_exp hΛF, le_sub_iff_add_le, le_div_iff₀ hηr]
      constructor <;> intro h <;> linarith
