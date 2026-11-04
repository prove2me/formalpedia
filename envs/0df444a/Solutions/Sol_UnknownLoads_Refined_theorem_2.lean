-- Prove2me | solution 1 for UnknownLoads.Refined.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T20:26:13.518218+00:00
-- url     : https://prove2.me/submissions/c2215611-c4ca-4be5-a76f-a6b590a85d69
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System
import Theorems.Thm_UnknownLoads_Refined_proposition_7
import Theorems.Thm_UnknownLoads_Refined_proposition_8
import Theorems.Thm_UnknownLoads_Refined_proposition_9
import Theorems.Thm_UnknownLoads_Refined_proposition_10
import Theorems.Thm_UnknownLoads_Refined_corollary_11
import Theorems.Thm_UnknownLoads_Refined_lemma_13

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined.T2Aux

open UnknownLoads.Refined

lemma rho_integrableOn (D : LoadData) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ D.T) :
    IntegrableOn D.rho (Icc s t) volume := by
  refine Measure.integrableOn_of_bounded (M := |D.C| / D.mu) (by simp) ?_ ?_
  · exact ((D.lam_measurable.div_const D.mu)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro r hr
    have h0 := D.lam_nonneg r ⟨hs.trans hr.1, hr.2.trans ht⟩
    have h1 := D.lam_le r ⟨hs.trans hr.1, hr.2.trans ht⟩
    simp only [LoadData.rho, Real.norm_eq_abs, abs_div, abs_of_pos D.mu_pos]
    exact div_le_div_of_nonneg_right (by rw [abs_of_nonneg h0]; exact h1.trans (le_abs_self _))
      D.mu_pos.le

lemma kernel_intervalIntegrable (D : LoadData) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ D.T) :
    IntervalIntegrable (fun r => D.rho r * D.mu * Real.exp (-D.mu * (t - r))) volume s t := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hst]
  have h := (rho_integrableOn D hs ht).mul_continuousOn
    (g' := fun r => D.mu * Real.exp (-D.mu * (t - r))) (by fun_prop) isCompact_Icc
  refine h.congr_fun (fun r _ => ?_) measurableSet_Icc
  simp only; ring

/-- `u(t) = u(s) e^{-µ(t-s)} + ∫_s^t ρ(r) µ e^{-µ(t-r)} dr` for `0 ≤ s ≤ t ≤ T`. -/
lemma fluid_split (D : LoadData) (q0 : ℕ → ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ D.T) :
    D.fluidU q0 t = D.fluidU q0 s * Real.exp (-D.mu * (t - s)) +
      ∫ r in s..t, D.rho r * D.mu * Real.exp (-D.mu * (t - r)) := by
  unfold LoadData.fluidU
  have h1 : IntervalIntegrable (fun r => D.rho r * D.mu * Real.exp (-D.mu * (t - r))) volume 0 s :=
    (kernel_intervalIntegrable D le_rfl (hs.trans hst) ht).mono_set (by
      rw [uIcc_of_le hs, uIcc_of_le (hs.trans hst)]; exact Icc_subset_Icc le_rfl hst)
  have h2 := kernel_intervalIntegrable D hs hst ht
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have h3 : (∫ r in (0:ℝ)..s, D.rho r * D.mu * Real.exp (-D.mu * (t - r))) =
      (∫ r in (0:ℝ)..s, D.rho r * D.mu * Real.exp (-D.mu * (s - r))) *
        Real.exp (-D.mu * (t - s)) := by
    rw [← intervalIntegral.integral_mul_const]
    congr 1; ext r
    rw [show -D.mu * (t - r) = -D.mu * (s - r) + -D.mu * (t - s) by ring, Real.exp_add]; ring
  rw [h3]
  have h4 : Real.exp (-D.mu * t) = Real.exp (-D.mu * s) * Real.exp (-D.mu * (t - s)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h4]; ring

lemma kernel_const_integral (D : LoadData) (c s t : ℝ) :
    (∫ r in s..t, c * D.mu * Real.exp (-D.mu * (t - r))) =
      c * (1 - Real.exp (-D.mu * (t - s))) := by
  have hd : ∀ r ∈ uIcc s t, HasDerivAt (fun r => c * Real.exp (-D.mu * (t - r)))
      (c * D.mu * Real.exp (-D.mu * (t - r))) r := by
    intro r _
    have h := ((((hasDerivAt_id' r).const_sub t).const_mul (-D.mu)).exp).const_mul c
    exact h.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp; ring

/-- (15)/(19): if `ρ ≥ c` on `[s, t] ⊂ [0, T]` then `u(t) ≥ c + (u(s) - c) e^{-µ(t-s)}`. -/
lemma fluid_lower (D : LoadData) (q0 : ℕ → ℝ) {s t c : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ D.T) (hc : ∀ r ∈ Icc s t, c ≤ D.rho r) :
    c + (D.fluidU q0 s - c) * Real.exp (-D.mu * (t - s)) ≤ D.fluidU q0 t := by
  rw [fluid_split D q0 hs hst ht]
  have hmono : (∫ r in s..t, c * D.mu * Real.exp (-D.mu * (t - r))) ≤
      ∫ r in s..t, D.rho r * D.mu * Real.exp (-D.mu * (t - r)) := by
    apply intervalIntegral.integral_mono_on hst
    · apply Continuous.intervalIntegrable; fun_prop
    · exact kernel_intervalIntegrable D hs hst ht
    · intro r hr
      have := hc r hr
      have hp : 0 ≤ D.mu * Real.exp (-D.mu * (t - r)) := by
        have := D.mu_pos; positivity
      nlinarith
  rw [kernel_const_integral] at hmono
  nlinarith


lemma occ_antitone {q : ℕ → ℝ} (hq : q ∈ OccupancySpace) : Antitone q :=
  antitone_nat_of_succ_le hq.2.2

lemma occ_zero_of_ge {q : ℕ → ℝ} (hq : q ∈ OccupancySpace) {B : ℕ} (hB : q (B + 1) = 0)
    {i : ℕ} (hi : B + 1 ≤ i) : q i = 0 :=
  le_antisymm (hB ▸ occ_antitone hq hi) (hq.2.1 i).1

lemma sum_range_shift (q : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range j, q (i + 1) = ∑ i ∈ Finset.Icc 1 j, q i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- For `q ∈ Q` vanishing from `B + 1` on: `u - v(j + 1) = ∑_{i=1}^{j} q(i)`. -/
lemma total_sub_tail {q : ℕ → ℝ} (hq : q ∈ OccupancySpace) {B : ℕ} (hB : q (B + 1) = 0)
    (j : ℕ) :
    (∑' i, q (i + 1)) - (∑' i, q (i + (j + 1))) = ∑ i ∈ Finset.Icc 1 j, q i := by
  have hs : Summable (fun i => q (i + 1)) := by
    apply summable_of_ne_finset_zero (s := Finset.range (B + 1))
    intro i hi
    simp only [Finset.mem_range, not_lt] at hi
    exact occ_zero_of_ge hq hB (by omega)
  rw [← hs.sum_add_tsum_nat_add j]
  have : (fun i => q (i + j + 1)) = fun i => q (i + (j + 1)) := by
    ext i; ring_nf
  simp only [this, add_sub_cancel_right, sum_range_shift]

lemma sum_Icc_le_card {q : ℕ → ℝ} (hq : q ∈ OccupancySpace) (j : ℕ) :
    ∑ i ∈ Finset.Icc 1 j, q i ≤ (j : ℝ) := by
  calc ∑ i ∈ Finset.Icc 1 j, q i ≤ ∑ _i ∈ Finset.Icc 1 j, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hq.2.1 i).2)
    _ = j := by simp

end UnknownLoads.Refined.T2Aux

open UnknownLoads.Refined UnknownLoads.Refined.T2Aux

set_option maxHeartbeats 1000000 in

theorem solution (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (γ₀ : ℝ) (hγ₀ : γ₀ ∈ Ioo (0 : ℝ) (1 / 2))
    (hα_lim : Tendsto α atTop (𝓝 1))
    (hα_rate : ∃ κ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, κ ≤ (n : ℝ) ^ γ₀ * (1 - α n))
    (m : ℕ) (a b : ℝ) (hbd : D.IsBounded sys.q0 m a b)
    (σ : ℝ) (hσ₁ : D.sigma sys.q0 a b m < σ) (hσ₂ : σ < b - a) :
    ∀ᵐ ω ∂P,
      (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (a + σ) b,
          |(sys.ℓ n ω t : ℝ) - (m : ℝ) * D.Δ| ≤ ε) ∧
      (∀ i : ℕ, i ≤ m * D.Δ → ∀ γ ∈ Ico (0 : ℝ) (1 / 2), ∀ ε > (0 : ℝ),
          ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (a + σ) b, (n : ℝ) ^ γ * |1 - sys.q n ω t i| ≤ ε) ∧
      Filter.limsup (fun n : ℕ => ⨆ t ∈ Icc (a + σ) b,
          (∑' i, ENNReal.ofReal (sys.q n ω t (i + ((m + 1) * D.Δ + 1)))) *
            ENNReal.ofReal (Real.exp (D.mu * (t - (a + σ))))) atTop ≤
        ENNReal.ofReal (D.fluidU sys.q0 (a + σ)) := by
  obtain ⟨BT, -, hnice⟩ := proposition_7 D sys
  filter_upwards [hnice] with ω hω
  have hbd' := hbd
  obtain ⟨ha0, hab, hbT, hmρ, hρM, -⟩ := hbd'
  have hμ := D.mu_pos
  set j : ℕ := m * D.Δ with hj_def
  have hjR : ((j : ℕ) : ℝ) = (m : ℝ) * D.Δ := by simp [hj_def]
  set ρmin := D.rhoMin a b with hρmin_def
  have hmΔ0 : (0 : ℝ) ≤ (m : ℝ) * D.Δ := by positivity
  have hρpos : 0 < ρmin := lt_of_le_of_lt hmΔ0 hmρ
  have hgap : 0 < ρmin - (m : ℝ) * D.Δ := by linarith
  set L := 1 / D.mu * Real.log (ρmin / (ρmin - m * D.Δ)) with hL_def
  have hsig : D.sigma sys.q0 a b m = L + D.sigmaBd sys.q0 a b m := by
    unfold LoadData.sigma LoadData.sigmaBd
    split_ifs <;> simp [hL_def, hρmin_def]
  have hbd0 : 0 ≤ D.sigmaBd sys.q0 a b m := by
    unfold LoadData.sigmaBd
    split_ifs
    · exact mul_nonneg (by positivity) (le_max_right _ _)
    · exact le_rfl
  have hL0 : 0 ≤ L := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    rw [le_div_iff₀ hgap]; linarith
  have hexpL : Real.exp (-D.mu * L) = (ρmin - m * D.Δ) / ρmin := by
    have : -D.mu * L = -Real.log (ρmin / (ρmin - m * D.Δ)) := by
      rw [hL_def]; field_simp
    rw [this, Real.exp_neg, Real.exp_log (div_pos hρpos hgap), inv_div]
  set δ := σ - D.sigma sys.q0 a b m with hδ_def
  have hδ : 0 < δ := by linarith
  set σ0 := D.sigmaBd sys.q0 a b m + δ / 3 with hσ0_def
  have hσ0pos : 0 < σ0 := by linarith
  set s := L + δ / 3 with hs_def
  set t0 := a + σ0 with ht0_def
  set t1 := t0 + s with ht1_def
  have ht01 : t0 < t1 := by linarith
  have ht1σ : t1 < a + σ := by linarith
  have ht1b : t1 ≤ b := by linarith
  have hσb : a + σ ≤ b := by linarith
  -- `ρ ≥ ρmin` on `[a, b]` and `ρ ≥ 0` on `[0, T]`
  have hρnn : ∀ r ∈ Icc 0 D.T, 0 ≤ D.rho r := fun r hr =>
    div_nonneg (D.lam_nonneg r hr) hμ.le
  have hρmin_le : ∀ r ∈ Icc a b, ρmin ≤ D.rho r := by
    intro r hr
    apply csInf_le ⟨0, ?_⟩ (mem_image_of_mem _ hr)
    rintro _ ⟨x, hx, rfl⟩
    exact hρnn x ⟨ha0.trans hx.1, hx.2.trans hbT⟩
  -- `εc := ρmin (1 - e^{-µ s}) - mΔ > 0`
  set εc := ρmin * (1 - Real.exp (-D.mu * s)) - m * D.Δ with hεc_def
  have hεc : 0 < εc := by
    have h1 : Real.exp (-D.mu * s) < Real.exp (-D.mu * L) := by
      apply Real.exp_lt_exp.mpr; nlinarith
    rw [hexpL] at h1
    have h2 : ρmin * Real.exp (-D.mu * s) < ρmin - m * D.Δ := by
      have := mul_lt_mul_of_pos_left h1 hρpos
      rwa [mul_div_cancel₀ _ hρpos.ne'] at this
    rw [hεc_def]; nlinarith
  -- unpack the nice path
  obtain ⟨-, hsolve, -, -, hQ, ⟨nT, hnT⟩, hq0lim, -, -⟩ := id hω
  have hocc : ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc 0 D.T, sys.q n ω t ∈ OccupancySpace :=
    fun n hn t ht => (hsolve n hn).1.2.2.1 t ht
  have hq0nn : ∀ i, 0 ≤ sys.q0 i := by
    intro i
    apply ge_of_tendsto (hq0lim i)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ((hocc n hn 0 ⟨le_rfl, D.T_pos.le⟩).2.1 i).1
  have hua : 0 ≤ D.fluidU sys.q0 a := by
    have h := fluid_lower D sys.q0 (s := 0) (t := a) (c := 0) le_rfl ha0 (hab.trans hbT)
      (fun r hr => hρnn r ⟨hr.1, hr.2.trans (hab.trans hbT)⟩)
    have h0 : D.fluidU sys.q0 0 = ∑' i, sys.q0 (i + 1) := by
      simp [LoadData.fluidU]
    have : 0 ≤ D.fluidU sys.q0 0 := h0 ▸ tsum_nonneg (fun i => hq0nn (i + 1))
    have := Real.exp_pos (-D.mu * (a - 0))
    nlinarith
  have hut0 : 0 < D.fluidU sys.q0 t0 := by
    have h := fluid_lower D sys.q0 (s := a) (t := t0) (c := ρmin) ha0 (by linarith) (by linarith)
      (fun r hr => hρmin_le r ⟨hr.1, by linarith [hr.2]⟩)
    have he : Real.exp (-D.mu * (t0 - a)) < 1 := by
      rw [← Real.exp_zero]; apply Real.exp_lt_exp.mpr; nlinarith
    have he0 := Real.exp_pos (-D.mu * (t0 - a))
    nlinarith
  -- Proposition 10 with `σ0`
  obtain ⟨nbd, hnbd⟩ := proposition_10 D sys γ₀ hγ₀ hα_lim hα_rate m a b hbd σ0
    (by linarith) BT ω hω
  -- (20): for all large `n`, `qₙ(ζ, mΔ) = 1` for some `ζ ∈ [t0, t1]`
  have hclaim : ∀ᶠ n : ℕ in atTop, ∃ ζ ∈ Icc t0 t1, sys.q n ω ζ j = 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · filter_upwards [eventually_ge_atTop 1] with n hn
      refine ⟨t0, ⟨le_rfl, ht01.le⟩, ?_⟩
      have : j = 0 := by simp [hj_def, hm]
      rw [this]
      exact (hocc n hn t0 ⟨by linarith, by linarith⟩).1
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ0, hφ0, hP⟩ := extraction_of_frequently_atTop
      (hcon.and_eventually (eventually_ge_atTop (max nbd (max nT 1))))
    obtain ⟨ψ, hψ, y, hy⟩ := hQ.1 φ0 hφ0
    set φ := φ0 ∘ ψ with hφ_def
    have hφ : StrictMono φ := hφ0.comp hψ
    have hφN : ∀ k, max nbd (max nT 1) ≤ φ k := fun k => (hP (ψ k)).2
    have hφ1 : ∀ k, 1 ≤ φ k := fun k => le_trans (by omega) (hφN k)
    have hb : ∀ t ∈ Icc t0 t1, ∀ k, sys.ℓ (φ k) ω t ≤ j ∧ sys.q (φ k) ω t j < 1 := by
      intro t ht k
      refine ⟨hnbd (φ k) (le_trans (by omega) (hφN k)) t ⟨ht.1, ht.2.trans ht1b⟩, ?_⟩
      have hle := ((hocc (φ k) (hφ1 k) t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2.1 j).2
      have hne : sys.q (φ k) ω t j ≠ 1 := fun h => (hP (ψ k)).1 ⟨t, ht, h⟩
      exact lt_of_le_of_ne hle hne
    obtain ⟨-, v, hv, hvlt⟩ := proposition_9 D sys BT ω hω φ hφ (hφ1 0) y (fun i => hy i) j
      ⟨m, hm, rfl⟩ t0 t1 (by linarith) ht01 (hbT.trans' ht1b) hb hut0
    have ht1mem : t1 ∈ Icc 0 D.T := ⟨by linarith, ht1b.trans hbT⟩
    have hU := ((proposition_8 D sys BT ω hω).tendsto_at ht1mem).comp hφ.tendsto_atTop
    have hV := hv.tendsto_at ht1mem
    have hε2 : 0 < εc / 2 := by linarith
    obtain ⟨k, hk1, hk2⟩ := ((Metric.tendsto_nhds.mp hU (εc / 2) hε2).and
      (Metric.tendsto_nhds.mp hV (εc / 2) hε2)).exists
    simp only [Function.comp_apply, Real.dist_eq] at hk1 hk2
    have hqk := hocc (φ k) (hφ1 k) t1 ht1mem
    have hBk := (hnT (φ k) (le_trans (by omega) (hφN k)) t1 ht1mem).1
    have hsum := total_sub_tail hqk hBk j
    have hle := sum_Icc_le_card hqk j
    have hvt1 := hvlt t1 ⟨ht01.le, le_rfl⟩
    have hut1 := fluid_lower D sys.q0 (s := t0) (t := t1) (c := ρmin) (by linarith) ht01.le
      (ht1b.trans hbT) (fun r hr => hρmin_le r ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    have hts : t1 - t0 = s := by rw [ht1_def]; ring
    rw [hts] at hvt1 hut1
    unfold System.totalMass at hk1
    unfold System.tailMass at hk2
    rw [hjR] at hle
    rw [abs_lt] at hk1 hk2
    have : ρmin * (1 - Real.exp (-D.mu * s)) = εc + m * D.Δ := by rw [hεc_def]; ring
    linarith [hk1.1, hk1.2, hk2.1, hk2.2]
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hclaim
  set N := max N1 (max nbd 1) with hN_def
  -- apply Lemma 13 along `φ k = k + N`
  have hex : ∀ k : ℕ, ∃ ζ ∈ Icc t0 t1, sys.q (k + N) ω ζ j = 1 :=
    fun k => hN1 (k + N) (by omega)
  choose ζ₁ hζ₁ hζq using hex
  have hφ : StrictMono (fun k : ℕ => k + N) := fun x y h => by simp [h]
  have hL13 := lemma_13 D sys γ₀ hγ₀ hα_lim hα_rate m a b hbd BT ω hω j ⟨m, le_rfl, rfl⟩
    (fun k => k + N) hφ (by omega) σ0 hσ0pos ζ₁ (fun _ => b)
    (fun k => ⟨(hζ₁ k).1, (hζ₁ k).2.trans ht1b, le_rfl⟩)
    (fun k => ⟨hζq k, fun t ht => hnbd (k + N) (by omega) t
      ⟨le_trans (hζ₁ k).1 ht.1, ht.2⟩⟩)
  have hconv : ∀ γ ∈ Ico (0 : ℝ) (1 / 2), ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (a + σ) b,
      sys.ℓ n ω t = j ∧ 1 - (n : ℝ) ^ (-γ) ≤ sys.q n ω t j := by
    intro γ hγ
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hL13 γ hγ)
    rw [eventually_atTop]
    refine ⟨K + N, fun n hn t ht => ?_⟩
    have h := hK (n - N) (by omega) t ⟨le_trans ((hζ₁ (n - N)).2.trans ht1σ.le) ht.1, ht.2⟩
    have hn' : n - N + N = n := by omega
    simp only [hn'] at h
    exact_mod_cast h
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    filter_upwards [hconv 0 ⟨le_rfl, by norm_num⟩] with n hn t ht
    rw [(hn t ht).1, hjR]
    simp [hε.le]
  · intro i hi γ hγ ε hε
    set γ' := (γ + 1 / 2) / 2 with hγ'_def
    have hγ' : γ' ∈ Ico (0 : ℝ) (1 / 2) := ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
    have hpos : 0 < γ' - γ := by linarith [hγ.2]
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(γ' - γ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
    filter_upwards [hconv γ' hγ', hlim.eventually (Iic_mem_nhds hε),
      eventually_ge_atTop (max N 1)] with n h1 h2 h3 t ht
    have hn0 : (0 : ℝ) < n := by
      have : 1 ≤ n := le_trans (le_max_right _ _) h3
      exact_mod_cast this
    have hqo := hocc n (le_trans (le_max_right _ _) h3) t
      ⟨by linarith [ht.1], ht.2.trans hbT⟩
    have hij : sys.q n ω t j ≤ sys.q n ω t i := occ_antitone hqo hi
    have hi1 := (hqo.2.1 i).2
    have habs : |1 - sys.q n ω t i| ≤ (n : ℝ) ^ (-γ') := by
      rw [abs_of_nonneg (by linarith)]
      linarith [(h1 t ht).2]
    have hmul : (n : ℝ) ^ γ * (n : ℝ) ^ (-γ') = (n : ℝ) ^ (-(γ' - γ)) := by
      rw [← Real.rpow_add hn0]; ring_nf
    calc (n : ℝ) ^ γ * |1 - sys.q n ω t i| ≤ (n : ℝ) ^ γ * (n : ℝ) ^ (-γ') :=
          mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (-(γ' - γ)) := hmul
      _ ≤ ε := h2
  · exact corollary_11 D sys γ₀ hγ₀ hα_lim hα_rate m a b hbd σ (by linarith) BT ω hω
