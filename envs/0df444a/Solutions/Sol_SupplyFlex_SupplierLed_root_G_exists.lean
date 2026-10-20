-- Prove2me | solution 1 for SupplyFlex.SupplierLed.root_G_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:40:43.75085+00:00
-- url     : https://prove2.me/submissions/360ecddf-ba54-4050-a98b-2ac5e991cc2b

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
theorem solution (M : Model) (hM : M.Std) (k : ℝ) (hk0 : 0 < k) (hkr : k ≤ M.r) :
    ∃ q : ℝ, 0 ≤ q ∧ M.r * G M.f q = k := by
  have hr := r_pos M hM
  obtain ⟨b, hb, hFb⟩ := exists_supp_Fbar_lt M hM (k / M.r) (div_pos hk0 hr)
  have hcont : ContinuousOn (fun q => M.r * G M.f q) (Set.Icc 0 b) := by
    unfold G
    refine continuousOn_const.mul (((Fbar_cont M hM).continuousOn).sub
      (continuousOn_id.mul (hM.f_cont.mono ?_)))
    intro x hx
    refine ⟨hx.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hx.2) hb.2⟩
  have h0 : M.r * G M.f 0 = M.r := by unfold G; rw [Fbar_zero M hM]; ring
  have hbval : M.r * G M.f b < k := by
    unfold G
    have : M.r * Fbar M.f b < k := by
      rwa [lt_div_iff₀ hr, mul_comm] at hFb
    nlinarith [mul_nonneg hb.1 (f_nonneg M hM b)]
  obtain ⟨q, hq, hqk⟩ := intermediate_value_Icc' hb.1 hcont ⟨hbval.le, by rw [h0]; exact hkr⟩
  exact ⟨q, hq.1, hqk⟩
