-- Prove2me | solution 1 for SupplyFlex.SupplierLed.root_qc_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:42:14.976944+00:00
-- url     : https://prove2.me/submissions/ad4293d1-638a-4b1f-a8d4-d8665cbda21a

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

open MeasureTheory SupplyFlex.SupplierLed

namespace T6Fbar

lemma f_nonneg (M : Model) (hM : M.Std) (x : ℝ) : 0 ≤ M.f x := by
  by_cases h : x ∈ supp M.abar
  · exact (hM.f_pos x h).le
  · rw [hM.f_zero x h]

lemma f_neg (M : Model) (hM : M.Std) (x : ℝ) (hx : x < 0) : M.f x = 0 :=
  hM.f_zero x (fun h => by linarith [h.1])

lemma r_pos (M : Model) (hM : M.Std) : 0 < M.r := by
  have := hM.assm1_r
  have : 0 < M.c / M.p := div_pos hM.c_pos hM.p_pos
  linarith

lemma Iic0 (M : Model) (hM : M.Std) : ∫ x in Set.Iic (0:ℝ), M.f x = 0 := by
  rw [integral_Iic_eq_integral_Iio]
  exact setIntegral_eq_zero_of_forall_eq_zero (fun x hx => f_neg M hM x hx)

/-- `F̄(x) = 1 − ∫₀ˣ f`. -/
lemma Fbar_eq (M : Model) (hM : M.Std) (x : ℝ) :
    Fbar M.f x = 1 - ∫ t in (0:ℝ)..x, M.f t := by
  have hi := hM.f_int.1
  have h1 := intervalIntegral.integral_Iic_add_Ioi (b := x) hi.integrableOn hi.integrableOn
  have h2 := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := x) hi.integrableOn
    hi.integrableOn
  rw [Iic0 M hM, sub_zero] at h2
  unfold Fbar
  rw [hM.f_int.2] at h1
  linarith

lemma Fbar_cont (M : Model) (hM : M.Std) : Continuous (Fbar M.f) := by
  have : Fbar M.f = fun x => 1 - ∫ t in (0:ℝ)..x, M.f t := funext (Fbar_eq M hM)
  rw [this]
  exact continuous_const.sub (intervalIntegral.continuous_primitive
    (fun a b => hM.f_int.1.intervalIntegrable) 0)

lemma Fbar_zero (M : Model) (hM : M.Std) : Fbar M.f 0 = 1 := by
  rw [Fbar_eq M hM]; simp

lemma Fbar_nonneg (M : Model) (hM : M.Std) (x : ℝ) : 0 ≤ Fbar M.f x :=
  setIntegral_nonneg measurableSet_Ioi (fun t _ => f_nonneg M hM t)

lemma Fbar_tendsto (M : Model) (hM : M.Std) :
    Filter.Tendsto (Fbar M.f) Filter.atTop (nhds 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := M.f) (s := fun x : ℝ => Set.Ioi x)
    (fun _ => measurableSet_Ioi) (fun a b hab => Set.Ioi_subset_Ioi hab)
    ⟨0, hM.f_int.1.integrableOn⟩
  have he : (⋂ n : ℝ, Set.Ioi n) = ∅ := by
    ext x; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    exact ⟨x, le_rfl⟩
  rw [he, Measure.restrict_empty, integral_zero_measure] at h
  exact h

/-- There are points of the support where `F̄` is arbitrarily small. -/
lemma exists_supp_Fbar_lt (M : Model) (hM : M.Std) (ε : ℝ) (hε : 0 < ε) :
    ∃ b, b ∈ supp M.abar ∧ Fbar M.f b < ε := by
  by_cases htop : M.abar = ⊤
  · obtain ⟨b, hb⟩ := Filter.eventually_atTop.1
      ((Fbar_tendsto M hM).eventually (gt_mem_nhds hε))
    refine ⟨max b 0, ⟨le_max_right _ _, by rw [htop]; exact ENNReal.ofReal_lt_top⟩,
      hb _ (le_max_left _ _)⟩
  · set a := M.abar.toReal with ha
    have hofa : ENNReal.ofReal a = M.abar := ENNReal.ofReal_toReal htop
    have hapos : 0 < a := ENNReal.toReal_pos hM.abar_pos.ne' htop
    have hFa : Fbar M.f a = 0 := by
      unfold Fbar
      refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => hM.f_zero t (fun h => ?_))
      have : ENNReal.ofReal a < ENNReal.ofReal t :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hapos.le).2 ht
      rw [hofa] at this
      exact absurd h.2 (not_lt.2 this.le)
    have hc := (Fbar_cont M hM).continuousAt (x := a)
    rw [ContinuousAt, hFa] at hc
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hε))
    set b := max 0 (a - δ / 2)
    have hb0 : 0 ≤ b := le_max_left _ _
    have hba : b < a := max_lt hapos (by linarith)
    refine ⟨b, ⟨hb0, ?_⟩, hball ?_⟩
    · rw [← hofa]; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb0).2 hba
    · rw [Real.dist_eq, abs_lt]
      constructor
      · have : a - δ / 2 ≤ b := le_max_right _ _
        linarith
      · linarith

end T6Fbar

open T6Fbar in
theorem solution (M : Model) (hM : M.Std) (qo qh : ℝ)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hs : M.s < wo M qo qh) :
    ∃ qc : ℝ, qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh) := by
  have hr := r_pos M hM
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hs0 : 0 < M.s := by
    have := hM.assm1_s; have : 0 < M.c / M.p := div_pos hM.c_pos hp; linarith
  by_cases hsr : M.s ≤ M.r
  · obtain ⟨hqh0, hqhe⟩ := hqh.1 hsr
    set φ : ℝ → ℝ := fun q => M.r * (M.p * q * Fbar M.f q + (1 - M.p) * qh * Fbar M.f qh) -
      M.s * (M.p * q + (1 - M.p) * qh) with hφ
    have hcont : Continuous φ := by
      have := Fbar_cont M hM
      simp only [hφ]; fun_prop
    -- value at `q̂*` is nonnegative
    have hφqh : 0 ≤ φ qh := by
      simp only [hφ]
      unfold G at hqhe
      nlinarith [mul_nonneg (mul_nonneg hqh0 hqh0) (mul_nonneg hr.le (f_nonneg M hM qh))]
    -- a large `Q` with `φ Q ≤ 0`
    set C := (1 - M.p) * qh * (M.r * Fbar M.f qh - M.s)
    have hev1 := (Fbar_tendsto M hM).eventually (gt_mem_nhds (div_pos hs0 (mul_pos hr two_pos)))
    obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 (hev1.and (Filter.eventually_ge_atTop
      (max qh (2 * |C| / (M.p * M.s) + 1))))
    have hQ1 := hQ Q le_rfl
    have hQqh : qh ≤ Q := le_trans (le_max_left _ _) hQ1.2
    have hQbig : 2 * |C| / (M.p * M.s) ≤ Q := by linarith [le_trans (le_max_right _ _) hQ1.2]
    have hφQ : φ Q ≤ 0 := by
      have hF : M.r * Fbar M.f Q < M.s / 2 := by
        have := hQ1.1; rw [lt_div_iff₀ (mul_pos hr two_pos)] at this; linarith
      have hQ0 : 0 ≤ Q := le_trans hqh0 hQqh
      have hps : 0 < M.p * M.s := mul_pos hp hs0
      have h2 : 2 * |C| ≤ Q * (M.p * M.s) := by rwa [div_le_iff₀ hps] at hQbig
      have hφ' : φ Q = M.p * Q * (M.r * Fbar M.f Q - M.s) + C := by simp only [hφ, C]; ring
      rw [hφ']
      have : M.p * Q * (M.r * Fbar M.f Q - M.s) ≤ M.p * Q * (-(M.s / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hp.le hQ0)
      nlinarith [le_abs_self C]
    obtain ⟨q, hq, hqv⟩ := intermediate_value_Icc' hQqh hcont.continuousOn ⟨hφQ, hφqh⟩
    refine ⟨q, hq.1, ?_⟩
    have : φ q = 0 := hqv
    simp only [hφ] at this
    linarith
  · have hrs : M.r < M.s := lt_of_not_ge hsr
    refine ⟨0, by rw [hqh.2 hrs], ?_⟩
    rw [hqh.2 hrs]; ring
