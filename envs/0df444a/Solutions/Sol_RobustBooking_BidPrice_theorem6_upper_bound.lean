-- Prove2me | solution 1 for RobustBooking.BidPrice.theorem6_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:41:45.221471+00:00
-- url     : https://prove2.me/submissions/144dc438-3781-483e-b497-7babba510c1e

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls
import Theorems.Thm_RobustBooking_BidPrice_theorem6_grid_bound

open MeasureTheory

namespace Aux_RB_thm6

open RobustBooking.BidPrice

lemma discountRatio_bounds (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    0 < discountRatio fmin fmax ∧ discountRatio fmin fmax < 1 := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  unfold discountRatio
  exact ⟨div_pos hfmin hfmax, (div_lt_one hfmax).mpr hf⟩

lemma gridFares_subset_Icc (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (m : ℕ) (hm : 2 ≤ m) :
    gridFares fmin fmax m ⊆ Set.Icc fmin fmax := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  obtain ⟨hr0, hr1⟩ := discountRatio_bounds fmin fmax hfmin hf
  have hm1 : 0 < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.ofNat_le_cast.mpr hm
    linarith
  rintro f ⟨i, hi1, him, rfl⟩
  have hi_ge : (1 : ℝ) ≤ (i : ℝ) := Nat.one_le_cast.mpr hi1
  have hi_le : (i : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr him
  have hexp0 : 0 ≤ ((i : ℝ) - 1) / ((m : ℝ) - 1) :=
    div_nonneg (by linarith) hm1.le
  have hexp1 : ((i : ℝ) - 1) / ((m : ℝ) - 1) ≤ 1 :=
    (div_le_one hm1).mpr (by linarith)
  have hpow_le : discountRatio fmin fmax ^ (((i : ℝ) - 1) / ((m : ℝ) - 1)) ≤ 1 := by
    calc discountRatio fmin fmax ^ (((i : ℝ) - 1) / ((m : ℝ) - 1))
        ≤ discountRatio fmin fmax ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hexp0
      _ = 1 := Real.rpow_zero _
  have hpow_ge : discountRatio fmin fmax ≤
      discountRatio fmin fmax ^ (((i : ℝ) - 1) / ((m : ℝ) - 1)) := by
    calc discountRatio fmin fmax
        = discountRatio fmin fmax ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ discountRatio fmin fmax ^ (((i : ℝ) - 1) / ((m : ℝ) - 1)) :=
          Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hexp1
  have hfmin_eq : fmax * discountRatio fmin fmax = fmin := by
    unfold discountRatio
    exact mul_div_cancel₀ fmin hfmax.ne'
  refine ⟨?_, ?_⟩
  · calc fmin = fmax * discountRatio fmin fmax := hfmin_eq.symm
      _ ≤ fmax * discountRatio fmin fmax ^ (((i : ℝ) - 1) / ((m : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hpow_ge hfmax.le
  · calc fmax * discountRatio fmin fmax ^ (((i : ℝ) - 1) / ((m : ℝ) - 1))
        ≤ fmax * 1 := mul_le_mul_of_nonneg_left hpow_le hfmax.le
      _ = fmax := mul_one fmax

lemma fmax_mem_gridFares (fmin fmax : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    fmax ∈ gridFares fmin fmax m := by
  refine ⟨1, le_rfl, by omega, ?_⟩
  simp

lemma offlineOpt_single_fmax (fmax n : ℝ) (hfmax : 0 < fmax) (hn : 0 < n) :
    offlineOpt n [⟨fmax, n, hn⟩] = fmax * n := by
  set I0 : List Request := [⟨fmax, n, hn⟩]
  unfold offlineOpt
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ => n, ⟨fun i => ⟨hn.le, ?_⟩, ?_⟩, ?_⟩
    · change Fin 1 at i
      fin_cases i
      exact le_rfl
    · show ∑ _i : Fin 1, n ≤ n
      simp
    · show fmax * n = ∑ i : Fin 1, (I0.get i).fare * n
      simp [I0]
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    calc ∑ i : Fin I0.length, (I0.get i).fare * x i
        ≤ ∑ i : Fin I0.length, fmax * x i := by
          refine Finset.sum_le_sum fun i _ => ?_
          change Fin 1 at i
          fin_cases i
          simp [I0]
      _ = fmax * ∑ i, x i := (Finset.mul_sum _ _ _).symm
      _ ≤ fmax * n := mul_le_mul_of_nonneg_left hx2 hfmax.le

lemma runFrom_nonneg (fmin fmax n : ℝ) (hfmin : 0 < fmin) (P : DetPolicy) :
    ∀ (I : List Request) (hist : List (Request × ℝ)),
      FaresIn (Set.Icc fmin fmax) I →
      (∀ e ∈ hist, 0 ≤ e.1.fare ∧ 0 ≤ e.2) →
      ∀ e ∈ runFrom P n hist I, 0 ≤ e.1.fare ∧ 0 ≤ e.2
  | [], hist, _, hhist => hhist
  | q :: qs, hist, hI, hhist => by
    have hq : q.fare ∈ Set.Icc fmin fmax := hI q List.mem_cons_self
    have hqs : FaresIn (Set.Icc fmin fmax) qs :=
      fun r hr => hI r (List.mem_cons_of_mem _ hr)
    set a := max 0 (min (P.decide hist q) (min q.qty (n - acceptedTotal hist)))
    have hhist' : ∀ e ∈ hist ++ [(q, a)], 0 ≤ e.1.fare ∧ 0 ≤ e.2 := by
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hhist e he
      · exact ⟨le_trans hfmin.le hq.1, le_max_left 0 _⟩
    exact runFrom_nonneg fmin fmax n hfmin P qs (hist ++ [(q, a)]) hqs hhist'

lemma list_sum_nonneg :
    ∀ (L : List (Request × ℝ)),
      (∀ e ∈ L, 0 ≤ e.1.fare ∧ 0 ≤ e.2) →
      0 ≤ (L.map fun e => e.1.fare * e.2).sum
  | [], _ => by simp
  | e :: es, hL => by
    have he := hL e List.mem_cons_self
    have ih := list_sum_nonneg es (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (mul_nonneg he.1 he.2) ih

lemma revenue_nonneg (fmin fmax n : ℝ) (hfmin : 0 < fmin) (P : DetPolicy)
    {I : List Request} (hI : FaresIn (Set.Icc fmin fmax) I) :
    0 ≤ revenue n P I :=
  list_sum_nonneg (run P n I) (runFrom_nonneg fmin fmax n hfmin P I [] hI (by simp))

lemma le_inv_one_sub_log_of_forall_grid (fmin fmax c : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hc : ∀ m : ℕ, 2 ≤ m →
      c ≤ 1 / ((m : ℝ) - ((m : ℝ) - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1)))) :
    c ≤ 1 / (1 - Real.log (discountRatio fmin fmax)) := by
  obtain ⟨hr0, hr1⟩ := discountRatio_bounds fmin fmax hfmin hf
  set r := discountRatio fmin fmax
  set L := -Real.log r
  have hlog_neg : Real.log r < 0 := Real.log_neg hr0 hr1
  have hL_pos : 0 < L := by dsimp [L]; linarith
  have h1L_pos : 0 < 1 + L := by linarith
  have h_step : ∀ m : ℕ, 2 ≤ m →
      ((m : ℝ) - 1) * (c * (1 + L) - 1) ≤ (1 - c) * L := by
    intro m hm
    set k : ℝ := (m : ℝ) - 1
    have hk1 : 1 ≤ k := by
      have : (2 : ℝ) ≤ (m : ℝ) := Nat.ofNat_le_cast.mpr hm
      dsimp [k]; linarith
    have hk_pos : 0 < k := by linarith
    have hkL_pos : 0 < k + L := by linarith
    have hexp_bound : 1 + L / k ≤ Real.exp (L / k) := by
      linarith [Real.add_one_le_exp (L / k)]
    have hrpow_mul_exp : r ^ (1 / k) * Real.exp (L / k) = 1 := by
      rw [Real.rpow_def_of_pos hr0, ← Real.exp_add]
      have h0 : Real.log r * (1 / k) + L / k = 0 := by dsimp [L]; ring
      rw [h0, Real.exp_zero]
    have hrpow_pos : 0 < r ^ (1 / k) := Real.rpow_pos_of_pos hr0 _
    have hrpow_le : r ^ (1 / k) * (k + L) ≤ k := by
      have h1 : r ^ (1 / k) * (1 + L / k) ≤ 1 := by
        calc r ^ (1 / k) * (1 + L / k)
            ≤ r ^ (1 / k) * Real.exp (L / k) :=
              mul_le_mul_of_nonneg_left hexp_bound hrpow_pos.le
          _ = 1 := hrpow_mul_exp
      have h2 : r ^ (1 / k) * (1 + L / k) * k ≤ 1 * k :=
        mul_le_mul_of_nonneg_right h1 hk_pos.le
      have h3 : r ^ (1 / k) * (1 + L / k) * k = r ^ (1 / k) * (k + L) := by
        field_simp
      linarith
    set Δm := (m : ℝ) - k * r ^ (1 / k)
    have hΔm_eq : Δm = 1 + k - k * r ^ (1 / k) := by dsimp [Δm, k]; ring
    have hΔm_kL : k * (1 + L) + L ≤ Δm * (k + L) := by
      have h1 : Δm * (k + L) = (1 + k) * (k + L) - k * (r ^ (1 / k) * (k + L)) := by
        rw [hΔm_eq]; ring
      nlinarith
    have hΔm_pos : 0 < Δm := by
      have : 0 < k * (1 + L) + L := by positivity
      nlinarith
    have hcm : c ≤ 1 / Δm := hc m hm
    have hc_Δm : c * Δm ≤ 1 := (le_div_iff₀ hΔm_pos).mp hcm
    have hc_prod : c * (Δm * (k + L)) ≤ k + L := by
      calc c * (Δm * (k + L)) = (c * Δm) * (k + L) := by ring
        _ ≤ 1 * (k + L) := mul_le_mul_of_nonneg_right hc_Δm hkL_pos.le
        _ = k + L := one_mul _
    -- What if c < 0?
    rcases le_or_gt 0 c with hc0 | hc_neg
    · have hc_lhs : c * (k * (1 + L) + L) ≤ k + L :=
        le_trans (mul_le_mul_of_nonneg_left hΔm_kL hc0) hc_prod
      linarith
    · have : c * (1 + L) - 1 < 0 := by nlinarith
      have : 0 < (1 - c) * L := by nlinarith
      nlinarith
  by_contra! h_gt
  have h1L_eq : 1 - Real.log r = 1 + L := by dsimp [L]; ring
  have h_gt' : 1 / (1 + L) < c := by
    rwa [h1L_eq] at h_gt
  have hδ : 0 < c * (1 + L) - 1 := by
    have := (div_lt_iff₀ h1L_pos).mp h_gt'
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 - c) * L / (c * (1 + L) - 1))
  have hm : 2 ≤ N + 2 := by omega
  have hstep := h_step (N + 2) hm
  have hcast : ((N + 2 : ℕ) : ℝ) - 1 = (N : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hstep
  have hN_gt : (1 - c) * L < ((N : ℝ) + 1) * (c * (1 + L) - 1) := by
    have h1 := (div_lt_iff₀ hδ).mp hN
    nlinarith
  linarith

lemma rand_Icc_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy)
    (hA : ∀ I : List Request, FaresIn (Set.Icc fmin fmax) I →
      Measurable fun ω => revenue n (A ω) I) :
    competitiveRatioRandOn (Set.Icc fmin fmax) n μ A ≤
      1 / (1 - Real.log (discountRatio fmin fmax)) := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  apply le_inv_one_sub_log_of_forall_grid fmin fmax _ hfmin hf
  intro m hm
  have hsub := gridFares_subset_Icc fmin fmax hfmin hf m hm
  have hA_grid : ∀ I : List Request, FaresIn (gridFares fmin fmax m) I →
      Measurable fun ω => revenue n (A ω) I :=
    fun I hI => hA I (fun q hq => hsub (hI q hq))
  have hgrid := (theorem6_grid_bound fmin fmax n hfmin hf hn m hm).2 μ A hA_grid
  refine le_trans ?_ hgrid
  unfold competitiveRatioRandOn
  apply csInf_le_csInf
  · refine ⟨0, ?_⟩
    rintro c ⟨I, hI, hopt, rfl⟩
    apply div_nonneg _ hopt.le
    exact integral_nonneg fun ω => revenue_nonneg fmin fmax n hfmin (A ω) hI
  · refine ⟨(∫ ω, revenue n (A ω) [⟨fmax, n, hn⟩] ∂μ) / offlineOpt n [⟨fmax, n, hn⟩],
      [⟨fmax, n, hn⟩], ?_, ?_, rfl⟩
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact fmax_mem_gridFares fmin fmax m hm
    · rw [offlineOpt_single_fmax fmax n hfmax hn]
      exact mul_pos hfmax hn
  · rintro c ⟨I, hI, hopt, rfl⟩
    exact ⟨I, fun q hq => hsub (hI q hq), hopt, rfl⟩

end Aux_RB_thm6

namespace RobustBooking.BidPrice

open Aux_RB_thm6

theorem theorem6_upper_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) :
    (∀ P : DetPolicy, competitiveRatioOn (Set.Icc fmin fmax) n P ≤
        1 / (1 - Real.log (discountRatio fmin fmax))) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → DetPolicy),
        (∀ I : List Request, FaresIn (Set.Icc fmin fmax) I →
          Measurable fun ω => revenue n (A ω) I) →
          competitiveRatioRandOn (Set.Icc fmin fmax) n μ A ≤
            1 / (1 - Real.log (discountRatio fmin fmax)) := by
  refine ⟨?_, fun μ _ A hA => rand_Icc_bound fmin fmax n hfmin hf hn μ A hA⟩
  intro P
  let μ0 : Measure Unit := Measure.dirac ()
  have hprob : IsProbabilityMeasure μ0 := Measure.dirac.isProbabilityMeasure
  have h1 := rand_Icc_bound fmin fmax n hfmin hf hn μ0 (fun _ => P) (fun _ _ => measurable_const)
  have heq : competitiveRatioOn (Set.Icc fmin fmax) n P =
      competitiveRatioRandOn (Set.Icc fmin fmax) n μ0 (fun _ => P) := by
    unfold competitiveRatioOn competitiveRatioRandOn
    congr 1
    ext c
    simp [μ0]
  rw [heq]
  exact h1

end RobustBooking.BidPrice

open RobustBooking.BidPrice MeasureTheory in
theorem solution (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) :
    (∀ P : DetPolicy, competitiveRatioOn (Set.Icc fmin fmax) n P ≤
        1 / (1 - Real.log (discountRatio fmin fmax))) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → DetPolicy),
        (∀ I : List Request, FaresIn (Set.Icc fmin fmax) I →
          Measurable fun ω => revenue n (A ω) I) →
          competitiveRatioRandOn (Set.Icc fmin fmax) n μ A ≤
            1 / (1 - Real.log (discountRatio fmin fmax)) :=
  theorem6_upper_bound fmin fmax n hfmin hf hn
