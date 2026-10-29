-- Prove2me | solution 1 for SmithRegenerative.Equilibrium.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T04:19:55.757993+00:00
-- url     : https://prove2.me/submissions/89a9df15-c380-4594-9946-388184a849ba

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal

set_option autoImplicit false

open MeasureTheory Filter Topology
open QueueingFundamentals.MG1

namespace SmithRegenerative.Equilibrium.RenewalLib

open SmithRegenerative.Equilibrium


noncomputable def expMom (l : ℝ) (ρ : Measure ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-(l * x))) ∂ρ

lemma measurable_expden (l : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(l * x)))) := by
  fun_prop

lemma expMom_conv (l : ℝ) (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    expMom l (ρ ∗ σ) = expMom l ρ * expMom l σ := by
  unfold expMom
  rw [Measure.lintegral_conv (measurable_expden l)]
  have : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-(l * (x + y)))) =
      ENNReal.ofReal (Real.exp (-(l * x))) * ENNReal.ofReal (Real.exp (-(l * y))) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
  simp only [this]
  simp only [lintegral_const_mul _ (measurable_expden l)]
  rw [lintegral_mul_const _ (measurable_expden l)]

lemma convPow_isProb (η : Measure ℝ) [IsProbabilityMeasure η] :
    ∀ n, IsProbabilityMeasure (convPow η n)
  | 0 => by rw [convPow]; infer_instance
  | n + 1 => by
      have := convPow_isProb η n
      rw [convPow]; infer_instance

lemma expMom_convPow (η : Measure ℝ) [IsProbabilityMeasure η] (l : ℝ) :
    ∀ n, expMom l (convPow η n) = expMom l η ^ n
  | 0 => by simp [convPow, expMom, lintegral_dirac]
  | n + 1 => by
    have := convPow_isProb η n
    simp only [convPow]
    rw [expMom_conv, expMom_convPow η l n, pow_succ]

lemma meas_Iic_le (l : ℝ) (hl : 0 < l) (ρ : Measure ℝ) (y : ℝ) :
    ρ (Set.Iic y) ≤ ENNReal.ofReal (Real.exp (l * y)) * expMom l ρ := by
  rw [expMom, ← lintegral_const_mul _ (measurable_expden l),
    ← lintegral_indicator_one measurableSet_Iic]
  refine lintegral_mono (fun x => ?_)
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs with hx
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ENNReal.one_le_ofReal,
      Real.one_le_exp_iff]
    have : x ≤ y := hx
    nlinarith
  · exact bot_le

lemma renewal_Iic_le (K F : Measure ℝ) [SFinite K] [IsProbabilityMeasure F]
    (l : ℝ) (hl : 0 < l) (y : ℝ) :
    renewalMeasure K F (Set.Iic y) ≤
      ENNReal.ofReal (Real.exp (l * y)) * expMom l K * (1 - expMom l F)⁻¹ := by
  rw [renewalMeasure, Measure.sum_apply _ measurableSet_Iic, ← ENNReal.tsum_geometric,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have := convPow_isProb F n
  refine (meas_Iic_le l hl _ y).trans (le_of_eq ?_)
  rw [expMom_conv, expMom_convPow F l n, mul_assoc]

/-- A cycle law has positive mass on `(0, ∞)`. -/
lemma cycle_Ioi_pos (F : Measure ℝ) (hF : IsCycleLaw F) : 0 < F (Set.Ioi 0) := by
  obtain ⟨hP, hneg, hne⟩ := hF
  rw [pos_iff_ne_zero]
  intro h0
  apply hne
  ext s hs
  have hc : F {(0:ℝ)}ᶜ = 0 := by
    have : ({(0:ℝ)}ᶜ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · intro h; exact lt_or_gt_of_ne h
      · rintro (h|h)
        · exact h.ne
        · exact h.ne'
    rw [this]; exact measure_union_null hneg h0
  have h1 : F {(0:ℝ)} = 1 := by
    have := measure_add_measure_compl (μ := F) (measurableSet_singleton (0:ℝ))
    rw [hc, add_zero, measure_univ] at this; exact this
  by_cases h : (0:ℝ) ∈ s
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_mem h, Pi.one_apply]
    apply le_antisymm (prob_le_one)
    rw [← h1]; exact measure_mono (Set.singleton_subset_iff.mpr h)
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h]
    exact measure_mono_null (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; rintro rfl; exact h hx) hc

lemma expMom_lt_one (F : Measure ℝ) (hF : IsCycleLaw F) (l : ℝ) (hl : 0 < l) :
    expMom l F < 1 := by
  have hP := hF.1
  have hneg := hF.2.1
  have hpos := cycle_Ioi_pos F hF
  -- some δ > 0 with F (Ioi δ) > 0
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ 0 < F (Set.Ioi δ) := by
    by_contra hcon
    push_neg at hcon
    have : Set.Ioi (0:ℝ) = ⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1)) := by
      ext x; simp only [Set.mem_Ioi, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩; exact lt_trans (by positivity) hn
    have hnull : F (⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1))) = 0 :=
      measure_iUnion_null (fun n => le_antisymm (hcon _ (by positivity)) bot_le)
    rw [this] at hpos
    exact hpos.ne' hnull
  -- split the integral
  have hae : ∀ᵐ x ∂F, 0 ≤ x := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hneg
  have hbound : ∀ᵐ x ∂F, ENNReal.ofReal (Real.exp (-(l * x))) ≤
      (Set.Ioi δ).indicator (fun _ => ENNReal.ofReal (Real.exp (-(l * δ)))) x +
        (Set.Ioi δ)ᶜ.indicator (fun _ => 1) x := by
    filter_upwards [hae] with x hx
    by_cases hxδ : x ∈ Set.Ioi δ
    · rw [Set.indicator_of_mem hxδ, Set.indicator_of_notMem (by simpa using hxδ), add_zero]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have : δ < x := hxδ
      nlinarith
    · rw [Set.indicator_of_notMem hxδ, Set.indicator_of_mem (by simpa using hxδ), zero_add]
      rw [ENNReal.ofReal_le_one]
      apply Real.exp_le_one_iff.mpr
      nlinarith
  calc expMom l F ≤ ∫⁻ x, ((Set.Ioi δ).indicator (fun _ => ENNReal.ofReal (Real.exp (-(l * δ)))) x +
        (Set.Ioi δ)ᶜ.indicator (fun _ => 1) x) ∂F := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (Real.exp (-(l * δ))) * F (Set.Ioi δ) + F (Set.Ioi δ)ᶜ := by
        rw [lintegral_add_left (Measurable.indicator measurable_const measurableSet_Ioi),
          lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ioi.compl]
        simp
    _ < F (Set.Ioi δ) + F (Set.Ioi δ)ᶜ := by
        apply ENNReal.add_lt_add_right (measure_ne_top _ _)
        have hlt : ENNReal.ofReal (Real.exp (-(l * δ))) < 1 := by
          rw [ENNReal.ofReal_lt_one]
          calc Real.exp (-(l * δ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
            _ = 1 := Real.exp_zero
        calc ENNReal.ofReal (Real.exp (-(l * δ))) * F (Set.Ioi δ)
            < 1 * F (Set.Ioi δ) := by
              rw [mul_comm, mul_comm 1]
              exact ENNReal.mul_lt_mul_right hδF.ne' (measure_ne_top _ _) hlt
          _ = F (Set.Ioi δ) := one_mul _
    _ = 1 := by rw [measure_add_measure_compl measurableSet_Ioi, measure_univ]

lemma expMom_le_mass (K : Measure ℝ) (hK0 : K (Set.Iio 0) = 0) (l : ℝ) (hl : 0 ≤ l) :
    expMom l K ≤ K Set.univ := by
  have hae : ∀ᵐ x ∂K, 0 ≤ x := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hK0
  calc expMom l K ≤ ∫⁻ _, 1 ∂K := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with x hx
        rw [ENNReal.ofReal_le_one]; apply Real.exp_le_one_iff.mpr; nlinarith
    _ = K Set.univ := by simp


/-! ## A1: convolution powers -/

lemma convPow_add (F : Measure ℝ) [IsProbabilityMeasure F] (m : ℕ) :
    ∀ n, convPow F (m + n) = (convPow F m) ∗ (convPow F n)
  | 0 => by
      have := convPow_isProb F m
      simp only [Nat.add_zero, convPow]
      exact (Measure.conv_dirac_zero _).symm
  | n + 1 => by
      have := convPow_isProb F m
      have := convPow_isProb F n
      rw [← Nat.add_assoc]
      simp only [convPow]
      rw [convPow_add F m n, Measure.conv_assoc]

/-! ## A2: the renewal measure from the origin -/

/-- `U = Σ_{n ≥ 0} F^{∗n}`. -/
noncomputable def U (F : Measure ℝ) : Measure ℝ := Measure.sum (convPow F)

lemma renewalMeasure_dirac (F : Measure ℝ) [IsProbabilityMeasure F] :
    renewalMeasure (Measure.dirac 0) F = U F := by
  unfold renewalMeasure U
  congr 1; funext n
  have := convPow_isProb F n
  exact Measure.dirac_zero_conv _

lemma lintegral_U (F : Measure ℝ) (g : ℝ → ENNReal) :
    ∫⁻ x, g x ∂(U F) = ∑' n, ∫⁻ x, g x ∂(convPow F n) := by
  unfold U; exact lintegral_sum_measure _ _

lemma U_sfinite (F : Measure ℝ) [IsProbabilityMeasure F] : SFinite (U F) := by
  haveI : ∀ n, SFinite (convPow F n) := fun n => by
    have := convPow_isProb F n; infer_instance
  unfold U; infer_instance

lemma measurable_shift_lintegral (μ : Measure ℝ) [SFinite μ] (g : ℝ → ENNReal)
    (hg : Measurable g) : Measurable (fun y => ∫⁻ x, g (y + x) ∂μ) :=
  (hg.comp measurable_add).lintegral_prod_right'

/-- `m`-step decomposition of the renewal measure. -/
lemma U_decomp (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ → ENNReal) (hg : Measurable g)
    (m : ℕ) :
    ∫⁻ x, g x ∂(U F) = ∑ j ∈ Finset.range m, ∫⁻ x, g x ∂(convPow F j) +
      ∫⁻ y, (∫⁻ x, g (y + x) ∂(U F)) ∂(convPow F m) := by
  rw [lintegral_U, ← Summable.sum_add_tsum_nat_add' (f := fun n => ∫⁻ x, g x ∂(convPow F n))
    (k := m) ENNReal.summable]
  refine congrArg (HAdd.hAdd _) ?_
  have hc : ∀ n, ∫⁻ x, g x ∂(convPow F (n + m)) =
      ∫⁻ y, (∫⁻ x, g (y + x) ∂(convPow F n)) ∂(convPow F m) := by
    intro n
    have := convPow_isProb F n
    have := convPow_isProb F m
    rw [Nat.add_comm, convPow_add, Measure.lintegral_conv hg]
  simp only [hc]
  have := convPow_isProb F m
  rw [← lintegral_tsum (fun n => by
    have := convPow_isProb F n
    exact (measurable_shift_lintegral (convPow F n) g hg).aemeasurable)]
  refine lintegral_congr fun y => ?_
  rw [lintegral_U]

/-- One-step renewal equation `U = δ₀ + U ∗ F`. -/
lemma U_renewal (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ x, g x ∂(U F) = g 0 + ∫⁻ x, (∫⁻ y, g (x + y) ∂F) ∂(U F) := by
  rw [lintegral_U, ← Summable.sum_add_tsum_nat_add' (f := fun n => ∫⁻ x, g x ∂(convPow F n))
    (k := 1) ENNReal.summable, Finset.sum_range_one]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp [convPow, lintegral_dirac]
  · have hc : ∀ n, ∫⁻ x, g x ∂(convPow F (n + 1)) =
        ∫⁻ x, (∫⁻ y, g (x + y) ∂F) ∂(convPow F n) := by
      intro n
      have := convPow_isProb F n
      simp only [convPow]
      rw [Measure.lintegral_conv hg]
    simp only [hc]
    rw [lintegral_U]

/-! ## A3: the inspection identity -/

lemma U_Iic_lt_top (F : Measure ℝ) (hF : IsCycleLaw F) (t : ℝ) : U F (Set.Iic t) < ⊤ := by
  have := hF.1
  rw [← renewalMeasure_dirac]
  refine lt_of_le_of_lt (renewal_Iic_le (Measure.dirac 0) F 1 one_pos t) ?_
  have h1 := expMom_lt_one F hF 1 one_pos
  have hK : expMom 1 (Measure.dirac (0:ℝ)) < ⊤ := by
    simp [expMom, lintegral_dirac]
  have h2 : (1 - expMom 1 F)⁻¹ ≠ ⊤ := by
    rw [Ne, ENNReal.inv_eq_top]; exact (tsub_pos_of_lt h1).ne'
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK)
    (lt_top_iff_ne_top.mpr h2)

lemma measurable_tailF (F : Measure ℝ) : Measurable (fun u : ℝ => F (Set.Ioi u)) := by
  apply Antitone.measurable
  intro a b hab
  exact measure_mono (Set.Ioi_subset_Ioi hab)

lemma measurable_cdfF (F : Measure ℝ) : Measurable (fun u : ℝ => F (Set.Iic u)) := by
  apply Monotone.measurable
  intro a b hab
  exact measure_mono (Set.Iic_subset_Iic.mpr hab)

/-- `∫_{[0,t]} (1 − F(t − s)) dU(s) = 1` for `t ≥ 0`. -/
lemma inspection (F : Measure ℝ) (hF : IsCycleLaw F) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ s in Set.Iic t, F (Set.Ioi (t - s)) ∂(U F) = 1 := by
  have hP := hF.1
  have hneg := hF.2.1
  have hmI : Measurable (fun s : ℝ => F (Set.Iic (t - s))) :=
    (measurable_cdfF F).comp (measurable_const.sub measurable_id)
  have hmO : Measurable (fun s : ℝ => F (Set.Ioi (t - s))) :=
    (measurable_tailF F).comp (measurable_const.sub measurable_id)
  -- renewal equation for the indicator of `Iic t`
  have hren := U_renewal F ((Set.Iic t).indicator 1)
    ((measurable_const.indicator measurableSet_Iic))
  rw [lintegral_indicator_one measurableSet_Iic] at hren
  have hin : ∀ x : ℝ, ∫⁻ y, (Set.Iic t).indicator 1 (x + y) ∂F = F (Set.Iic (t - x)) := by
    intro x
    have : (fun y => (Set.Iic t).indicator (1 : ℝ → ENNReal) (x + y)) =
        (Set.Iic (t - x)).indicator 1 := by
      funext y
      by_cases h : y ≤ t - x
      · rw [Set.indicator_of_mem (show y ∈ Set.Iic (t - x) from h),
          Set.indicator_of_mem (show x + y ∈ Set.Iic t by simp only [Set.mem_Iic]; linarith)]
        rfl
      · rw [Set.indicator_of_notMem (show y ∉ Set.Iic (t - x) from h),
          Set.indicator_of_notMem (show x + y ∉ Set.Iic t by simp only [Set.mem_Iic]; linarith)]
    rw [this, lintegral_indicator_one measurableSet_Iic]
  simp only [hin, Set.indicator_of_mem (show (0:ℝ) ∈ Set.Iic t from ht), Pi.one_apply] at hren
  have hsupp : ∫⁻ x, F (Set.Iic (t - x)) ∂(U F) = ∫⁻ x in Set.Iic t, F (Set.Iic (t - x)) ∂(U F) := by
    refine (setLIntegral_eq_of_support_subset ?_).symm
    intro x hx
    by_contra hxt
    simp only [Set.mem_Iic, not_le] at hxt
    apply hx
    exact measure_mono_null (Set.Iic_subset_Iio.mpr (by linarith)) hneg
  have hsplit : U F (Set.Iic t) = ∫⁻ x in Set.Iic t, F (Set.Iic (t - x)) ∂(U F) +
      ∫⁻ x in Set.Iic t, F (Set.Ioi (t - x)) ∂(U F) := by
    rw [← lintegral_add_left hmI]
    have : ∀ x, F (Set.Iic (t - x)) + F (Set.Ioi (t - x)) = 1 := by
      intro x
      rw [← Set.compl_Iic, measure_add_measure_compl measurableSet_Iic, measure_univ]
    simp only [this, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      one_mul]
  have hfin : ∫⁻ x in Set.Iic t, F (Set.Iic (t - x)) ∂(U F) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (U_Iic_lt_top F hF t).ne ?_
    rw [hsplit]; exact le_self_add
  rw [hsupp, hsplit, add_comm (1 : ENNReal)] at hren
  exact (ENNReal.add_right_inj hfin).mp hren.symm |>.symm

/-! ## A4: uniform bound for the renewal measure of an interval -/

/-- `m(B) = ∫_0^B (1 − F(u)) du`. -/
noncomputable def mB (F : Measure ℝ) (B : ℝ) : ENNReal := ∫⁻ u in Set.Ioc 0 B, F (Set.Ioi u)

lemma shift_Ioc (φ : ℝ → ENNReal) (s B : ℝ) :
    ∫⁻ t in Set.Ioc s (s + B), φ (t - s) = ∫⁻ u in Set.Ioc 0 B, φ u := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
    ← lintegral_sub_right_eq_self (fun u => (Set.Ioc 0 B).indicator φ u) s]
  congr 1; funext t
  by_cases h : t ∈ Set.Ioc s (s + B)
  · have h' : t - s ∈ Set.Ioc 0 B := by
      simp only [Set.mem_Ioc] at h ⊢; constructor <;> linarith [h.1, h.2]
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : t - s ∉ Set.Ioc 0 B := by
      simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at h ⊢
      rcases h with h | h
      · left; linarith
      · right; linarith
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

lemma window_bound (F : Measure ℝ) (hF : IsCycleLaw F) (x A B : ℝ) (hx : 0 ≤ x) (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    U F (Set.Icc x (x + A)) * mB F B ≤ ENNReal.ofReal (A + B) := by
  have hP := hF.1
  set I := Set.Icc x (x + A + B) with hI
  set k : ℝ × ℝ → ENNReal := fun p => if p.2 ≤ p.1 then F (Set.Ioi (p.1 - p.2)) else 0 with hk
  have hkm : Measurable k :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      ((measurable_tailF F).comp (measurable_fst.sub measurable_snd)) measurable_const
  have hvol : ENNReal.ofReal (A + B) = ∫⁻ t in I, ∫⁻ s, k (t, s) ∂(U F) := by
    have h1 : ENNReal.ofReal (A + B) = ∫⁻ _ in I, (1 : ENNReal) := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul,
        hI, Real.volume_Icc]
      congr 1; ring
    rw [h1]
    refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    have ht0 : 0 ≤ t := le_trans hx ht.1
    rw [← inspection F hF t ht0, ← lintegral_indicator measurableSet_Iic]
    congr 1
  have := U_sfinite F
  rw [hvol, lintegral_lintegral_swap hkm.aemeasurable]
  calc U F (Set.Icc x (x + A)) * mB F B
      = ∫⁻ _ in Set.Icc x (x + A), mB F B ∂(U F) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, mul_comm]
    _ ≤ ∫⁻ s in Set.Icc x (x + A), (∫⁻ t in I, k (t, s)) ∂(U F) := by
        refine setLIntegral_mono' measurableSet_Icc (fun s hs => ?_)
        have hsub : Set.Ioc s (s + B) ⊆ I := by
          intro t ht
          simp only [hI, Set.mem_Icc, Set.mem_Ioc] at hs ht ⊢
          constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
        calc mB F B = ∫⁻ t in Set.Ioc s (s + B), F (Set.Ioi (t - s)) := by
              rw [mB, shift_Ioc (fun u => F (Set.Ioi u)) s B]
          _ = ∫⁻ t in Set.Ioc s (s + B), k (t, s) := by
              refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
              simp only [hk, if_pos ht.1.le]
          _ ≤ ∫⁻ t in I, k (t, s) := lintegral_mono_set hsub
    _ ≤ ∫⁻ s, (∫⁻ t in I, k (t, s)) ∂(U F) := setLIntegral_le_lintegral _ _


/-! ## B: the support semigroup and its asymptotic density -/

/-- Points of `[0,∞)` all of whose neighbourhoods are charged by some `F^{∗m}`. -/
def S (F : Measure ℝ) : Set ℝ :=
  {σ | 0 ≤ σ ∧ ∀ η > 0, ∃ m : ℕ, 0 < convPow F m (Metric.ball σ η)}

lemma conv_ball_ge (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (a b r1 r2 : ℝ) :
    μ (Metric.ball a r1) * ν (Metric.ball b r2) ≤ (μ ∗ ν) (Metric.ball (a + b) (r1 + r2)) := by
  rw [Measure.conv, Measure.map_apply measurable_add Metric.isOpen_ball.measurableSet,
    ← Measure.prod_prod]
  refine measure_mono ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [Set.mem_preimage, Metric.mem_ball] at hx hy ⊢
  calc dist (x + y) (a + b) ≤ dist x a + dist y b := dist_add_add_le x y a b
    _ < r1 + r2 := add_lt_add hx hy

lemma zero_mem_S (F : Measure ℝ) : (0 : ℝ) ∈ S F := by
  refine ⟨le_rfl, fun η hη => ⟨0, ?_⟩⟩
  rw [convPow, Measure.dirac_apply_of_mem (Metric.mem_ball_self hη)]
  exact one_pos

lemma add_mem_S (F : Measure ℝ) [IsProbabilityMeasure F] {a b : ℝ} (ha : a ∈ S F)
    (hb : b ∈ S F) : a + b ∈ S F := by
  refine ⟨add_nonneg ha.1 hb.1, fun η hη => ?_⟩
  obtain ⟨m1, h1⟩ := ha.2 (η / 2) (half_pos hη)
  obtain ⟨m2, h2⟩ := hb.2 (η / 2) (half_pos hη)
  refine ⟨m1 + m2, ?_⟩
  have := convPow_isProb F m1
  have := convPow_isProb F m2
  rw [convPow_add]
  have hle := conv_ball_ge (convPow F m1) (convPow F m2) a b (η / 2) (η / 2)
  rw [add_halves] at hle
  exact lt_of_lt_of_le (ENNReal.mul_pos h1.ne' h2.ne') hle

lemma nsmul_mem_S (F : Measure ℝ) [IsProbabilityMeasure F] {a : ℝ} (ha : a ∈ S F) :
    ∀ n : ℕ, n • a ∈ S F
  | 0 => by rw [zero_smul]; exact zero_mem_S F
  | n + 1 => by rw [succ_nsmul]; exact add_mem_S F (nsmul_mem_S F ha n) ha

lemma convPow_one (F : Measure ℝ) [IsProbabilityMeasure F] : convPow F 1 = F := by
  simp only [convPow]; exact Measure.dirac_zero_conv F

lemma S_compl_null (F : Measure ℝ) [IsProbabilityMeasure F] (hneg : F (Set.Iio 0) = 0) :
    F (S F)ᶜ = 0 := by
  have hT : F ((S F)ᶜ ∩ Set.Ici 0) = 0 := by
    refine measure_null_of_locally_null _ (fun x hx => ?_)
    have hx0 : 0 ≤ x := hx.2
    have hxS : ¬ (∀ η > 0, ∃ m : ℕ, 0 < convPow F m (Metric.ball x η)) :=
      fun h => hx.1 ⟨hx0, h⟩
    simp only [not_forall, not_exists, not_lt, nonpos_iff_eq_zero] at hxS
    obtain ⟨η, hη, hm⟩ := hxS
    refine ⟨Metric.ball x η, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hη), ?_⟩
    have h1 := hm 1
    rwa [convPow_one] at h1
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hneg hT)
  by_cases h0 : 0 ≤ x
  · exact Or.inr ⟨hx, h0⟩
  · exact Or.inl (lt_of_not_ge h0)

/-- The group of differences of `S F`. -/
def Hgrp (F : Measure ℝ) [IsProbabilityMeasure F] : AddSubgroup ℝ where
  carrier := {z | ∃ a ∈ S F, ∃ b ∈ S F, z = a - b}
  zero_mem' := ⟨0, zero_mem_S F, 0, zero_mem_S F, by ring⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a + c, add_mem_S F ha hc, b + d, add_mem_S F hb hd, by ring⟩
  neg_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, by ring⟩

lemma exists_small_gap (F : Measure ℝ) (hF : IsCycleLaw F) (hper : IsAperiodic F) (δ : ℝ)
    (hδ : 0 < δ) : ∃ a ∈ S F, ∃ b ∈ S F, 0 < b - a ∧ b - a < δ := by
  have hP := hF.1
  rcases AddSubgroup.dense_or_cyclic (Hgrp F) with hd | ⟨c, hc⟩
  · obtain ⟨z, hz, hz'⟩ := hd.exists_between hδ
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    exact ⟨b, hb, a, ha, hz'.1, hz'.2⟩
  · exfalso
    apply hper
    have hSc : ∀ σ ∈ S F, ∃ n : ℕ, σ = (n : ℝ) * |c| := by
      intro σ hσ
      have hmem : σ ∈ Hgrp F := ⟨σ, hσ, 0, zero_mem_S F, by ring⟩
      rw [hc, AddSubgroup.mem_closure_singleton] at hmem
      obtain ⟨k, hk⟩ := hmem
      rw [zsmul_eq_mul] at hk
      refine ⟨k.natAbs, ?_⟩
      have hcast : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hcast, ← abs_mul, hk, abs_of_nonneg hσ.1]
    have hset : ∀ ϖ : ℝ, (∀ σ ∈ S F, ∃ n : ℕ, σ = (n : ℝ) * ϖ) →
        F {x : ℝ | ∃ n : ℕ, x = (n : ℝ) * ϖ} = 1 := by
      intro ϖ hϖ
      refine le_antisymm prob_le_one ?_
      have hc0 : F {x : ℝ | ∃ n : ℕ, x = (n : ℝ) * ϖ}ᶜ = 0 :=
        measure_mono_null (fun x hx hxS => hx (hϖ x hxS))
          (S_compl_null F hF.2.1)
      calc (1 : ENNReal) = F Set.univ := measure_univ.symm
        _ ≤ F {x : ℝ | ∃ n : ℕ, x = (n : ℝ) * ϖ} + F {x : ℝ | ∃ n : ℕ, x = (n : ℝ) * ϖ}ᶜ :=
            measure_univ_le_add_compl _
        _ = _ := by rw [hc0, add_zero]
    by_cases hc0 : c = 0
    · refine ⟨1, one_pos, hset 1 (fun σ hσ => ?_)⟩
      obtain ⟨n, hn⟩ := hSc σ hσ
      exact ⟨0, by rw [hn, hc0]; simp⟩
    · exact ⟨|c|, abs_pos.mpr hc0, hset |c| hSc⟩

/-- Asymptotic density of the support semigroup. -/
lemma S_dense (F : Measure ℝ) (hF : IsCycleLaw F) (hper : IsAperiodic F) (δ : ℝ) (hδ : 0 < δ) :
    ∃ T0 : ℝ, ∀ x ≥ T0, ∃ σ ∈ S F, x ≤ σ ∧ σ ≤ x + δ := by
  have hP := hF.1
  obtain ⟨a, ha, b, hb, hg0, hgδ⟩ := exists_small_gap F hF hper δ hδ
  have ha0 := ha.1
  have hb0 : 0 < b := by linarith
  refine ⟨max 0 (a * b / (b - a)), fun x hx => ?_⟩
  have hx0 : 0 ≤ x := le_trans (le_max_left _ _) hx
  have hxab : a * b / (b - a) ≤ x := le_trans (le_max_right _ _) hx
  rw [div_le_iff₀ hg0] at hxab
  set n : ℕ := ⌈x / b⌉₊ with hn
  have hnb : x ≤ n * b := by
    have := Nat.le_ceil (x / b); rw [← hn, div_le_iff₀ hb0] at this; linarith
  have hna : (n : ℝ) * a ≤ x := by
    have h1 : (n : ℝ) < x / b + 1 := Nat.ceil_lt_add_one (div_nonneg hx0 hb0.le)
    have h2 : (n : ℝ) * a ≤ (x / b + 1) * a := mul_le_mul_of_nonneg_right h1.le ha0
    have h3 : (x / b + 1) * a ≤ x := by
      have : (x / b + 1) * a = (x * a + a * b) / b := by field_simp
      rw [this, div_le_iff₀ hb0]; nlinarith
    linarith
  set j : ℕ := ⌈(x - n * a) / (b - a)⌉₊ with hj
  have hj1 : x - n * a ≤ j * (b - a) := by
    have := Nat.le_ceil ((x - n * a) / (b - a)); rw [← hj, div_le_iff₀ hg0] at this; linarith
  have hj2 : (j : ℝ) * (b - a) < x - n * a + (b - a) := by
    have h := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ x - n * a) hg0.le)
    rw [← hj] at h
    have h' := mul_lt_mul_of_pos_right h hg0
    rw [add_mul, div_mul_cancel₀ _ hg0.ne', one_mul] at h'; linarith
  have hjn : j ≤ n := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hg0]; nlinarith
  refine ⟨(n - j) • a + j • b, add_mem_S F (nsmul_mem_S F ha _) (nsmul_mem_S F hb _), ?_, ?_⟩
  · rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hjn]; nlinarith
  · rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hjn]; nlinarith


/-! ## C: windows and the maximum principle -/

lemma convPow_Iio (F : Measure ℝ) [IsProbabilityMeasure F] (hneg : F (Set.Iio 0) = 0) :
    ∀ n, convPow F n (Set.Iio 0) = 0
  | 0 => by
      rw [convPow, Measure.dirac_apply' _ measurableSet_Iio]
      simp
  | n + 1 => by
      have := convPow_isProb F n
      rw [convPow, Measure.conv, Measure.map_apply measurable_add measurableSet_Iio]
      refine measure_mono_null (t := (Set.Iio 0 ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Iio 0)) ?_
        (measure_union_null ?_ ?_)
      · intro p hp
        simp only [Set.mem_preimage, Set.mem_Iio] at hp
        simp only [Set.mem_union, Set.mem_prod, Set.mem_Iio, Set.mem_univ, and_true, true_and]
        by_contra hc
        push Not at hc
        linarith [hc.1, hc.2]
      · rw [Measure.prod_prod, convPow_Iio F hneg n, zero_mul]
      · rw [Measure.prod_prod, hneg, mul_zero]

lemma U_Iio (F : Measure ℝ) [IsProbabilityMeasure F] (hneg : F (Set.Iio 0) = 0) :
    U F (Set.Iio 0) = 0 := by
  rw [U, Measure.sum_apply _ measurableSet_Iio]
  simp [convPow_Iio F hneg]

/-- The renewal measure of the window `(t, t+h]`. -/
noncomputable def W (F : Measure ℝ) (h t : ℝ) : ENNReal := U F (Set.Ioc t (t + h))

lemma W_mul_mB_le (F : Measure ℝ) (hF : IsCycleLaw F) (h B : ℝ) (hh : 0 ≤ h) (hB : 0 ≤ B)
    (t : ℝ) : W F h t * mB F B ≤ ENNReal.ofReal (h + B) := by
  have hP := hF.1
  rcases le_or_gt 0 t with ht | ht
  · refine le_trans (mul_le_mul_left (measure_mono Set.Ioc_subset_Icc_self) _) ?_
    exact window_bound F hF t h B ht hh hB
  · have hsub : Set.Ioc t (t + h) ⊆ Set.Iio 0 ∪ Set.Icc 0 (0 + h) := by
      intro x hx
      rcases lt_or_ge x 0 with hx0 | hx0
      · exact Or.inl hx0
      · exact Or.inr ⟨hx0, by linarith [hx.2]⟩
    have hW : W F h t ≤ U F (Set.Icc 0 (0 + h)) := by
      calc W F h t ≤ U F (Set.Iio 0 ∪ Set.Icc 0 (0 + h)) := measure_mono hsub
        _ ≤ U F (Set.Iio 0) + U F (Set.Icc 0 (0 + h)) := measure_union_le _ _
        _ = U F (Set.Icc 0 (0 + h)) := by rw [U_Iio F hF.2.1, zero_add]
    exact le_trans (mul_le_mul_left hW _) (window_bound F hF 0 h B le_rfl hh hB)

lemma exists_tail_pos (F : Measure ℝ) (hF : IsCycleLaw F) : ∃ u0 > 0, 0 < F (Set.Ioi u0) := by
  by_contra hno
  simp only [not_exists, not_and, not_lt, nonpos_iff_eq_zero] at hno
  have h0 := cycle_Ioi_pos F hF
  have hU : Set.Ioi (0:ℝ) ⊆ ⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1)) := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (Set.mem_Ioi.mp hx)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have : F (Set.Ioi 0) = 0 :=
    measure_mono_null hU (measure_iUnion_null (fun n => hno _ (by positivity)))
  rw [this] at h0; exact lt_irrefl _ h0

lemma mB_ne_top (F : Measure ℝ) [IsProbabilityMeasure F] (B : ℝ) : mB F B ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in Set.Ioc 0 B, (1 : ENNReal)) ?_ (setLIntegral_mono'
    measurableSet_Ioc (fun u _ => prob_le_one))
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul,
    Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

lemma exists_mB_pos (F : Measure ℝ) (hF : IsCycleLaw F) : ∃ B > 0, mB F B ≠ 0 := by
  obtain ⟨u0, hu0, hpos⟩ := exists_tail_pos F hF
  refine ⟨u0, hu0, ?_⟩
  have hle : ∫⁻ _ in Set.Ioc 0 u0, F (Set.Ioi u0) ≤ mB F u0 :=
    setLIntegral_mono' measurableSet_Ioc (fun u hu => measure_mono (Set.Ioi_subset_Ioi hu.2))
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc, sub_zero] at hle
  exact (lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' (by simpa using hu0)) hle).ne'

/-- Uniform bound on windows. -/
lemma W_bdd (F : Measure ℝ) (hF : IsCycleLaw F) (h : ℝ) (hh : 0 ≤ h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, W F h t ≠ ⊤ ∧ (W F h t).toReal ≤ C := by
  have hP := hF.1
  obtain ⟨B, hB, hmB⟩ := exists_mB_pos F hF
  have hmt := mB_ne_top F B
  set Cw : ENNReal := ENNReal.ofReal (h + B) / mB F B with hCw
  have hCw_top : Cw ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hmB
  have hle : ∀ t, W F h t ≤ Cw := fun t =>
    (ENNReal.le_div_iff_mul_le (Or.inl hmB) (Or.inl hmt)).mpr (W_mul_mB_le F hF h B hh hB.le t)
  refine ⟨Cw.toReal, ENNReal.toReal_nonneg, fun t => ⟨ne_top_of_le_ne_top hCw_top (hle t), ?_⟩⟩
  exact ENNReal.toReal_mono hCw_top (hle t)

lemma measurable_W (F : Measure ℝ) [IsProbabilityMeasure F] (h : ℝ) : Measurable (W F h) := by
  have := U_sfinite F
  set k : ℝ × ℝ → ENNReal := fun p => if p.1 < p.2 ∧ p.2 ≤ p.1 + h then 1 else 0 with hk
  have hkm : Measurable k := Measurable.ite ((measurableSet_lt measurable_fst measurable_snd).inter
    (measurableSet_le measurable_snd (measurable_fst.add_const h))) measurable_const
    measurable_const
  have : W F h = fun t => ∫⁻ x, k (t, x) ∂(U F) := by
    funext t
    rw [W, ← lintegral_indicator_one measurableSet_Ioc]
    congr 1; funext x
    simp only [hk, Set.indicator_apply, Set.mem_Ioc, Pi.one_apply]
  rw [this]; exact hkm.lintegral_prod_right'

lemma W_decomp (F : Measure ℝ) [IsProbabilityMeasure F] (h t : ℝ) (m : ℕ) :
    W F h t = ∑ j ∈ Finset.range m, convPow F j (Set.Ioc t (t + h)) +
      ∫⁻ y, W F h (t - y) ∂(convPow F m) := by
  have hd := U_decomp F ((Set.Ioc t (t + h)).indicator 1)
    (measurable_const.indicator measurableSet_Ioc) m
  simp only [lintegral_indicator_one measurableSet_Ioc] at hd
  rw [W, hd]
  congr 1
  congr 1; funext y
  rw [W, ← lintegral_indicator_one measurableSet_Ioc]
  congr 1; funext x
  simp only [Set.indicator_apply, Set.mem_Ioc, Pi.one_apply]
  congr 1
  apply propext
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma tendsto_real_Ioi (P : Measure ℝ) [IsFiniteMeasure P] :
    Tendsto (fun t => P.real (Set.Ioi t)) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := P) (s := fun t : ℝ => Set.Ioi t)
    (fun _ => measurableSet_Ioi.nullMeasurableSet) (fun a b hab => Set.Ioi_subset_Ioi hab)
    ⟨0, measure_ne_top _ _⟩
  have he : (⋂ n : ℝ, Set.Ioi n) = ∅ := by
    ext x; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]; exact ⟨x, le_rfl⟩
  rw [he, measure_empty] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def, measureReal_def] using this

/-- Real windows and their renewal representation. -/
noncomputable def fw (F : Measure ℝ) (h t : ℝ) : ℝ := (W F h t).toReal

lemma fw_rep (F : Measure ℝ) (hF : IsCycleLaw F) (h : ℝ) (hh : 0 ≤ h) (m : ℕ) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ t, fw F h t = e t + ∫ y, fw F h (t - y) ∂(convPow F m) := by
  have hP := hF.1
  obtain ⟨C, -, hC⟩ := W_bdd F hF h hh
  refine ⟨fun t => ∑ j ∈ Finset.range m, (convPow F j).real (Set.Ioc t (t + h)), ?_, ?_⟩
  · rw [show (0:ℝ) = ∑ j ∈ Finset.range m, (0:ℝ) by simp]
    refine tendsto_finsetSum _ (fun j _ => ?_)
    have := convPow_isProb F j
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_real_Ioi (convPow F j)) (fun t => measureReal_nonneg) (fun t => ?_)
    exact measureReal_mono Set.Ioc_subset_Ioi_self
  · intro t
    have := convPow_isProb F m
    have hm : Measurable (fun y => W F h (t - y)) :=
      (measurable_W F h).comp (measurable_const.sub measurable_id)
    rw [fw, W_decomp F h t m, ENNReal.toReal_add, ENNReal.toReal_sum]
    · congr 1
      rw [← integral_toReal hm.aemeasurable (Filter.Eventually.of_forall
        (fun y => lt_top_iff_ne_top.mpr (hC (t - y)).1))]
      rfl
    · intro j _
      have := convPow_isProb F j
      exact measure_ne_top _ _
    · exact ENNReal.sum_ne_top.mpr (fun j _ => by
        have := convPow_isProb F j; exact measure_ne_top _ _)
    · intro htop
      have hle := W_decomp F h t m
      exact (hC t).1 (by rw [hle]; exact le_top.antisymm (htop ▸ le_add_self))

/-! ### the pick lemma -/

lemma pick (P : Measure ℝ) [IsProbabilityMeasure P] (φ : ℝ → ℝ) (hφm : Measurable φ) (C : ℝ)
    (hC : ∀ x, |φ x| ≤ C) (t L ε ε' τ e v : ℝ) (hL : 0 ≤ L) (hε' : 0 ≤ ε') (hε : 0 < ε)
    (G : Set ℝ) (hG : MeasurableSet G) (hGc : P.real Gᶜ ≤ τ)
    (hup : ∀ y ∈ G, φ (t - y) ≤ L + ε')
    (hv : v ≤ e + ∫ y, φ (t - y) ∂P) (hv' : L - ε' ≤ v) (A : Set ℝ) (hA : MeasurableSet A)
    (hAbig : 2 * ε' + e + (C + L + ε + 2 * ε') * τ < ε * P.real A) :
    ∃ y ∈ A, L - ε ≤ φ (t - y) := by
  by_contra hno
  push Not at hno
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hτ0 : 0 ≤ τ := le_trans measureReal_nonneg hGc
  set K := C + L + ε' with hK
  have hK0 : 0 ≤ K := by linarith
  have hbound : ∀ y, φ (t - y) ≤ (L + ε') - (ε + ε') * (A ∩ G).indicator 1 y +
      K * Gᶜ.indicator 1 y := by
    intro y
    by_cases hyG : y ∈ G
    · have hyGc : y ∉ Gᶜ := fun h => h hyG
      rw [Set.indicator_of_notMem hyGc]
      by_cases hyA : y ∈ A
      · rw [Set.indicator_of_mem (show y ∈ A ∩ G from ⟨hyA, hyG⟩)]
        simp only [Pi.one_apply, mul_one, mul_zero, add_zero]
        linarith [hno y hyA]
      · rw [Set.indicator_of_notMem (show y ∉ A ∩ G from fun h => hyA h.1)]
        simp only [mul_zero, sub_zero, add_zero]
        exact hup y hyG
    · rw [Set.indicator_of_mem (show y ∈ Gᶜ from hyG),
        Set.indicator_of_notMem (show y ∉ A ∩ G from fun h => hyG h.2)]
      simp only [Pi.one_apply, mul_one, mul_zero, sub_zero]
      have := (abs_le.mp (hC (t - y))).2
      linarith
  have hφi : Integrable (fun y => φ (t - y)) P :=
    Integrable.of_bound ((hφm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) C
      (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hC _))
  have hi1 : Integrable ((A ∩ G).indicator (1 : ℝ → ℝ)) P :=
    (integrable_const (1:ℝ)).indicator (hA.inter hG)
  have hi2 : Integrable (Gᶜ.indicator (1 : ℝ → ℝ)) P :=
    (integrable_const (1:ℝ)).indicator hG.compl
  have ha : Integrable (fun y => L + ε' - (ε + ε') * (A ∩ G).indicator (1 : ℝ → ℝ) y) P :=
    (integrable_const _).sub (hi1.const_mul _)
  have hb : Integrable (fun y => K * Gᶜ.indicator (1 : ℝ → ℝ) y) P := hi2.const_mul _
  have hI : ∫ y, φ (t - y) ∂P ≤ (L + ε') - (ε + ε') * P.real (A ∩ G) + K * P.real Gᶜ := by
    calc ∫ y, φ (t - y) ∂P ≤ ∫ y, ((L + ε') - (ε + ε') * (A ∩ G).indicator 1 y +
          K * Gᶜ.indicator 1 y) ∂P := integral_mono hφi (ha.add hb) hbound
      _ = (L + ε') - (ε + ε') * P.real (A ∩ G) + K * P.real Gᶜ := by
          rw [integral_add ha hb,
            integral_sub (integrable_const _) (hi1.const_mul _), integral_const_mul,
            integral_const_mul, integral_indicator_one (hA.inter hG),
            integral_indicator_one hG.compl, integral_const]
          simp
  have hAG : P.real A ≤ P.real (A ∩ G) + P.real Gᶜ := by
    calc P.real A ≤ P.real ((A ∩ G) ∪ Gᶜ) := measureReal_mono (fun y hy => by
            by_cases hyG : y ∈ G
            · exact Or.inl ⟨hy, hyG⟩
            · exact Or.inr hyG)
      _ ≤ P.real (A ∩ G) + P.real Gᶜ := measureReal_union_le _ _
  have hAG0 : 0 ≤ P.real (A ∩ G) := measureReal_nonneg
  have h1 : ε * (P.real A - τ) ≤ ε * P.real (A ∩ G) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  have h2 : K * P.real Gᶜ ≤ K * τ := mul_le_mul_of_nonneg_left hGc hK0
  have h3 : 0 ≤ ε' * P.real (A ∩ G) := mul_nonneg hε' hAG0
  have h4 : 0 ≤ ε' * τ := mul_nonneg hε' hτ0
  nlinarith


/-! ## D1: the maximum principle along a finite set of semigroup points -/

lemma maxp (F : Measure ℝ) [IsProbabilityMeasure F] (f : ℝ → ℝ) (hfm : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C)
    (hrep : ∀ m : ℕ, ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ t, f t ≤ e t + ∫ y, f (t - y) ∂(convPow F m))
    (L : ℝ) (hL : 0 ≤ L) (hev : ∀ ε' > 0, ∀ᶠ t in atTop, f t ≤ L + ε')
    (hfreq : ∀ ε' > 0, ∃ᶠ t in atTop, L - ε' ≤ f t)
    {N : ℕ} (σ : Fin N → ℝ) (hσ : ∀ i, σ i ∈ S F) (η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ t in atTop, ∀ i, ∃ y ∈ Metric.ball (σ i) η, L - ε ≤ f (t - y) := by
  have hm : ∀ i, ∃ m : ℕ, 0 < convPow F m (Metric.ball (σ i) η) := fun i => (hσ i).2 η hη
  choose m hmpos using hm
  set g : Fin N → ℝ := fun i => (convPow F (m i)).real (Metric.ball (σ i) η) with hg
  have hgpos : ∀ i, 0 < g i := by
    intro i
    have := convPow_isProb F (m i)
    exact ENNReal.toReal_pos (hmpos i).ne' (measure_ne_top _ _)
  set p : ℝ := 1 / (1 + ∑ i, 1 / g i) with hp
  have hS0 : 0 ≤ ∑ i, 1 / g i := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hgpos i)).le)
  have hp0 : 0 < p := by rw [hp]; positivity
  have hpi : ∀ i, p ≤ g i := by
    intro i
    rw [hp, div_le_iff₀ (by positivity)]
    have h1 : 1 / g i ≤ ∑ j, 1 / g j :=
      Finset.single_le_sum (f := fun j => 1 / g j) (fun j _ => (one_div_pos.mpr (hgpos j)).le)
        (Finset.mem_univ i)
    have h2 : g i * (1 / g i) = 1 := mul_one_div_cancel (hgpos i).ne'
    have h3 : g i * (1 / g i) ≤ g i * ∑ j, 1 / g j := mul_le_mul_of_nonneg_left h1 (hgpos i).le
    nlinarith [hgpos i]
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  set ε' : ℝ := ε * p / 8 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.mp (hev ε' hε'0)
  choose e he_t he_rep using fun i => hrep (m i)
  set K' : ℝ := C + L + ε + 2 * ε' with hK'
  have hev2 : ∀ᶠ t in atTop, ∀ i, e i t < ε * p / 4 ∧
      K' * (convPow F (m i)).real (Set.Ioi (t + -s0)) < ε * p / 4 := by
    rw [Filter.eventually_all]
    intro i
    have := convPow_isProb F (m i)
    refine ((he_t i).eventually (gt_mem_nhds (by positivity))).and ?_
    have hτ : Tendsto (fun t => K' * (convPow F (m i)).real (Set.Ioi (t + -s0))) atTop
        (𝓝 (K' * 0)) :=
      ((tendsto_real_Ioi _).comp (tendsto_atTop_add_const_right atTop (-s0) tendsto_id)).const_mul K'
    rw [mul_zero] at hτ
    exact hτ.eventually (gt_mem_nhds (by positivity))
  refine ((hfreq ε' hε'0).and_eventually hev2).mono ?_
  rintro t ⟨hft, hall⟩ i
  have := convPow_isProb F (m i)
  obtain ⟨he1, he2⟩ := hall i
  have hgi : ε * p ≤ ε * g i := mul_le_mul_of_nonneg_left (hpi i) hε.le
  refine pick (convPow F (m i)) f hfm C hC t L ε ε' ((convPow F (m i)).real (Set.Ioi (t + -s0)))
    (e i t) (f t) hL hε'0.le hε (Set.Iic (t + -s0)) measurableSet_Iic (by rw [Set.compl_Iic])
    (fun y hy => hs0 (t - y) (by simp only [Set.mem_Iic] at hy; linarith)) (he_rep i t) hft
    (Metric.ball (σ i) η) measurableSet_ball ?_
  simp only [hg] at hgi
  linarith

/-! ## D2: Blackwell upper bound -/

lemma fw_nonneg (F : Measure ℝ) (h t : ℝ) : 0 ≤ fw F h t := ENNReal.toReal_nonneg

lemma fw_upper_core (F : Measure ℝ) (hF : IsCycleLaw F) (hper : IsAperiodic F) (h : ℝ)
    (hh : 0 < h) (L : ℝ) (hL : 0 ≤ L) (hev : ∀ ε' > 0, ∀ᶠ t in atTop, fw F h t ≤ L + ε')
    (hfreq : ∀ ε' > 0, ∃ᶠ t in atTop, L - ε' ≤ fw F h t) (B : ℝ) (hB : 0 ≤ B)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * (L - ε) * (mB F B).toReal ≤ N * (h + 3 * η) + B := by
  have hP := hF.1
  obtain ⟨C, hC0, hC⟩ := W_bdd F hF h hh.le
  obtain ⟨T0, hT0⟩ := S_dense F hF hper η hη
  set d : ℝ := h + 3 * η with hd
  have hd0 : 0 < d := by positivity
  set T1 : ℝ := max T0 0 with hT1
  have hσ : ∀ i : Fin N, ∃ σ ∈ S F, T1 + i * d ≤ σ ∧ σ ≤ T1 + i * d + η := fun i =>
    hT0 _ (le_trans (le_max_left _ _) (le_add_of_nonneg_right (by positivity)))
  choose σ hσS hσ1 hσ2 using hσ
  have hfm : Measurable (fw F h) := (measurable_W F h).ennreal_toReal
  have hCabs : ∀ x, |fw F h x| ≤ C := fun x => by
    rw [abs_of_nonneg (fw_nonneg F h x)]; exact (hC x).2
  have hrep : ∀ m : ℕ, ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ t, fw F h t ≤ e t + ∫ y, fw F h (t - y) ∂(convPow F m) := fun m => by
    obtain ⟨e, he, hrep⟩ := fw_rep F hF h hh.le m
    exact ⟨e, he, fun t => (hrep t).le⟩
  have hfr := maxp F (fw F h) hfm C hCabs hrep L hL hev hfreq σ hσS η hη ε hε
  obtain ⟨t, hbig, ht⟩ := (hfr.and_eventually (Filter.eventually_ge_atTop
    (T1 + N * d + 2 * η))).exists
  choose y hyball hyL using hbig
  have hyb : ∀ i : Fin N, T1 + i * d - η < y i ∧ y i < T1 + i * d + 2 * η := by
    intro i
    have h1 := hyball i
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h1
    have := hσ1 i; have := hσ2 i
    constructor <;> linarith [h1.1, h1.2]
  have hiN : ∀ i : Fin N, (i : ℝ) + 1 ≤ N := fun i => by
    have := i.isLt; exact_mod_cast this
  have hT10 : 0 ≤ T1 := le_max_right _ _
  set x : ℝ := t - T1 - N * d + d - 2 * η with hx
  set A : ℝ := N * d with hA
  have hx0 : 0 ≤ x := by rw [hx]; nlinarith
  have hA0 : 0 ≤ A := by positivity
  have hsub : ∀ i : Fin N, Set.Ioc (t - y i) (t - y i + h) ⊆ Set.Icc x (x + A) := by
    intro i z hz
    have := hyb i; have := hiN i
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have hid : (i : ℝ) * d ≤ (N - 1) * d := mul_le_mul_of_nonneg_right (by linarith) hd0.le
    have hid0 : 0 ≤ (i : ℝ) * d := mul_nonneg hi0 hd0.le
    simp only [Set.mem_Ioc, Set.mem_Icc] at hz ⊢
    constructor <;> nlinarith [hz.1, hz.2]
  have hdisj : Pairwise (Function.onFun Disjoint (fun i : Fin N => Set.Ioc (t - y i) (t - y i + h))) := by
    have key : ∀ i j : Fin N, i < j → y i + h < y j := by
      intro i j hij
      have hij' : (i : ℝ) + 1 ≤ j := by
        have : (i : ℕ) + 1 ≤ j := hij; exact_mod_cast this
      have := hyb i; have := hyb j
      have : ((i : ℝ) + 1) * d ≤ (j : ℝ) * d := mul_le_mul_of_nonneg_right hij' hd0.le
      nlinarith
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have := key i j hlt
      exact Set.disjoint_left.mpr (fun z hz1 hz2 => by
        simp only [Set.mem_Ioc] at hz1 hz2; linarith [hz1.1, hz2.2])
    · have := key j i hlt
      exact Set.disjoint_left.mpr (fun z hz1 hz2 => by
        simp only [Set.mem_Ioc] at hz1 hz2; linarith [hz1.2, hz2.1])
  have hsum : ∑ i, W F h (t - y i) ≤ U F (Set.Icc x (x + A)) := by
    show ∑ i, U F (Set.Ioc (t - y i) (t - y i + h)) ≤ _
    rw [← measure_biUnion_finset (hdisj.set_pairwise _) (fun i _ => measurableSet_Ioc)]
    exact measure_mono (Set.iUnion₂_subset (fun i _ => hsub i))
  have hwb := window_bound F hF x A B hx0 hA0 hB
  have hfin : ∀ i, W F h (t - y i) ≠ ⊤ := fun i => (hC _).1
  have hE : (∑ i, W F h (t - y i)) * mB F B ≤ ENNReal.ofReal (A + B) :=
    le_trans (mul_le_mul_left hsum _) hwb
  have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_sum
    (fun i _ => hfin i)] at hR
  have hm0 : 0 ≤ (mB F B).toReal := ENNReal.toReal_nonneg
  have hlow : (N : ℝ) * (L - ε) ≤ ∑ i, fw F h (t - y i) := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hyL i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  simp only [fw] at hlow
  have := mul_le_mul_of_nonneg_right hlow hm0
  rw [hA] at hR
  linarith


/-! ## D3: the mean as the integral of the tail -/

lemma mean_eq (F : Measure ℝ) (hF : IsCycleLaw F) :
    mean F = ∫⁻ u in Set.Ioi 0, F (Set.Ioi u) := by
  have hnn : 0 ≤ᵐ[F] (fun x : ℝ => x) := by
    refine ae_iff.mpr ?_
    have hs : {a : ℝ | ¬ (0 : ℝ → ℝ) a ≤ a} = Set.Iio 0 := by ext; simp
    rw [hs]; exact hF.2.1
  rw [mean, lintegral_eq_lintegral_meas_lt F hnn measurable_id.aemeasurable]
  rfl

lemma mB_le_mean (F : Measure ℝ) (hF : IsCycleLaw F) (B : ℝ) : mB F B ≤ mean F := by
  rw [mean_eq F hF, mB]; exact lintegral_mono_set Set.Ioc_subset_Ioi_self

lemma mean_le_iSup_mB (F : Measure ℝ) (hF : IsCycleLaw F) : mean F ≤ ⨆ n : ℕ, mB F n := by
  rw [mean_eq F hF]
  have hφ := measurable_tailF F
  have hmono : Monotone (fun n : ℕ => (Set.Ioc (0:ℝ) n).indicator (fun u => F (Set.Ioi u))) := by
    intro a b hab u
    exact Set.indicator_le_indicator_of_subset
      (Set.Ioc_subset_Ioc_right (by exact_mod_cast hab)) (fun _ => bot_le) u
  have hsup : (Set.Ioi (0:ℝ)).indicator (fun u => F (Set.Ioi u)) =
      fun u => ⨆ n : ℕ, (Set.Ioc (0:ℝ) n).indicator (fun u => F (Set.Ioi u)) u := by
    funext u
    refine le_antisymm ?_ (iSup_le fun n => Set.indicator_le_indicator_of_subset
      Set.Ioc_subset_Ioi_self (fun _ => bot_le) u)
    by_cases hu : u ∈ Set.Ioi (0:ℝ)
    · refine le_iSup_of_le ⌈u⌉₊ (le_of_eq ?_)
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem
        (show u ∈ Set.Ioc (0:ℝ) ((⌈u⌉₊ : ℕ) : ℝ) from ⟨hu, Nat.le_ceil u⟩)]
    · rw [Set.indicator_of_notMem hu]; exact bot_le
  rw [← lintegral_indicator measurableSet_Ioi, hsup,
    lintegral_iSup (fun n => hφ.indicator measurableSet_Ioc) hmono]
  refine iSup_le fun n => le_iSup_of_le n (le_of_eq ?_)
  rw [mB, lintegral_indicator measurableSet_Ioc]

lemma mean_pos (F : Measure ℝ) (hF : IsCycleLaw F) : 0 < mean F := by
  obtain ⟨B, -, hB⟩ := exists_mB_pos F hF
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hB) (mB_le_mean F hF B)

/-! ## D4: Blackwell upper bound -/

lemma fw_upper (F : Measure ℝ) (hF : IsCycleLaw F) (hper : IsAperiodic F) (h : ℝ) (hh : 0 < h)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ t in atTop, fw F h t ≤ h * (mean F)⁻¹.toReal + ε := by
  have hP := hF.1
  obtain ⟨C, hC0, hC⟩ := W_bdd F hF h hh.le
  set L := Filter.limsup (fw F h) atTop with hLdef
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fw F h) := isBoundedUnder_of ⟨C, fun t => (hC t).2⟩
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fw F h) :=
    isCoboundedUnder_le_of_le atTop (fun t => fw_nonneg F h t)
  have hL0 : 0 ≤ L := le_limsup_of_le hbdd (fun b hb => by
    obtain ⟨t, ht⟩ := hb.exists; exact le_trans (fw_nonneg F h t) ht)
  have hev : ∀ ε' > 0, ∀ᶠ t in atTop, fw F h t ≤ L + ε' := fun ε' hε' =>
    (eventually_lt_of_limsup_lt (by linarith) hbdd).mono (fun t ht => ht.le)
  have hfreq : ∀ ε' > 0, ∃ᶠ t in atTop, L - ε' ≤ fw F h t := fun ε' hε' =>
    (frequently_lt_of_lt_limsup hcob (by linarith)).mono (fun t ht => ht.le)
  -- `L · m(B) ≤ h` for every `B ≥ 0`
  have hkey : ∀ B : ℝ, 0 ≤ B → L * (mB F B).toReal ≤ h := by
    intro B hB
    set m := (mB F B).toReal with hm
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    by_contra hcon
    push Not at hcon
    set gap := L * m - h with hgap
    have hgap0 : 0 < gap := by linarith
    set ε1 := gap / (3 * (m + 1)) with hε1
    have hε10 : 0 < ε1 := by positivity
    have hε1m : ε1 * m ≤ gap / 3 := by
      rw [hε1, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    set η := gap / 9 with hη
    have hη0 : 0 < η := by positivity
    set N : ℕ := ⌈3 * B / gap⌉₊ + 1 with hN
    have hN1 : 1 ≤ N := Nat.le_add_left 1 _
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
    have hBN : B < N * (gap / 3) := by
      have h1 : 3 * B / gap < N := by
        rw [hN]; push_cast; exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
      rw [div_lt_iff₀ hgap0] at h1; linarith
    have hc := fw_upper_core F hF hper h hh L hL0 hev hfreq B hB ε1 η hε10 hη0 N hN1
    have e1 : (N:ℝ) * (L - ε1) * m = N * (L * m) - N * (ε1 * m) := by ring
    have e2 : (N:ℝ) * (h + 3 * η) = N * h + N * (gap / 3) := by rw [hη]; ring
    have e3 : (N:ℝ) * (L * m) = N * h + 3 * (N * (gap / 3)) := by rw [hgap]; ring
    have h4 : (N:ℝ) * (ε1 * m) ≤ N * (gap / 3) := mul_le_mul_of_nonneg_left hε1m hNpos.le
    rw [e1, e2, e3] at hc
    linarith
  -- pass to `mean F`
  have hE : ENNReal.ofReal L * mean F ≤ ENNReal.ofReal h := by
    have hmono : ENNReal.ofReal L * mean F ≤ ENNReal.ofReal L * ⨆ n : ℕ, mB F n := by
      gcongr; exact mean_le_iSup_mB F hF
    refine le_trans hmono ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun n => ?_
    rw [← ENNReal.ofReal_toReal (mB_ne_top F n), ← ENNReal.ofReal_mul hL0]
    exact ENNReal.ofReal_le_ofReal (hkey n (Nat.cast_nonneg n))
  have hLc : L ≤ h * (mean F)⁻¹.toReal := by
    by_cases htop : mean F = ⊤
    · rw [htop] at hE
      have hL' : L ≤ 0 := by
        by_contra hpos
        push Not at hpos
        rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr hpos).ne'] at hE
        exact (not_le.mpr ENNReal.ofReal_lt_top) hE
      rw [htop, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero]; exact hL'
    · have hmp := mean_pos F hF
      have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL0, ENNReal.toReal_ofReal hh.le] at hR
      have hmr : 0 < (mean F).toReal := ENNReal.toReal_pos hmp.ne' htop
      rw [ENNReal.toReal_inv, ← div_eq_mul_inv, le_div_iff₀ hmr]
      exact hR
  exact (hev ε hε).mono (fun t ht => by linarith)


/-! ## D5: tools for the lower bound -/

lemma W_add (F : Measure ℝ) (g t : ℝ) (hg : 0 ≤ g) :
    ∀ k : ℕ, W F ((k : ℝ) * g) t = ∑ i ∈ Finset.range k, W F g (t + i * g)
  | 0 => by simp [W]
  | k + 1 => by
      rw [Finset.sum_range_succ, ← W_add F g t hg k]
      have hu : Set.Ioc t (t + ((k + 1 : ℕ) : ℝ) * g) =
          Set.Ioc t (t + k * g) ∪ Set.Ioc (t + k * g) (t + k * g + g) := by
        rw [Set.Ioc_union_Ioc_eq_Ioc (by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
          (by linarith)]
        congr 1; push_cast; ring
      simp only [W]
      rw [hu, measure_union (Set.disjoint_left.mpr fun z hz1 hz2 => by
        simp only [Set.mem_Ioc] at hz1 hz2; linarith [hz1.2, hz2.1]) measurableSet_Ioc]

/-- Discretised inspection identity. -/
lemma inspection_le_sum (F : Measure ℝ) (hF : IsCycleLaw F) (T g : ℝ) (hT : 0 ≤ T)
    (hg : 0 < g) :
    1 ≤ ∑' j : ℕ, F (Set.Ioi ((j : ℝ) * g)) * W F g (T - ((j : ℝ) + 1) * g) := by
  set I : ℕ → Set ℝ := fun j => Set.Ioc (T - ((j : ℝ) + 1) * g) (T - (j : ℝ) * g) with hI
  have hcov : Set.Iic T ⊆ ⋃ j, I j := by
    intro s hs
    simp only [Set.mem_Iic] at hs
    have hq : 0 ≤ (T - s) / g := div_nonneg (by linarith) hg.le
    refine Set.mem_iUnion.mpr ⟨⌊(T - s) / g⌋₊, ?_⟩
    have h1 := Nat.floor_le hq
    have h2 := Nat.lt_floor_add_one ((T - s) / g)
    rw [le_div_iff₀ hg] at h1
    rw [div_lt_iff₀ hg] at h2
    simp only [hI, Set.mem_Ioc]
    constructor <;> linarith
  have hdisj : Pairwise (Function.onFun Disjoint I) := by
    have key : ∀ i j : ℕ, i < j → Disjoint (I i) (I j) := by
      intro i j hij
      have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      refine Set.disjoint_left.mpr (fun z hz1 hz2 => ?_)
      simp only [hI, Set.mem_Ioc] at hz1 hz2
      nlinarith [hz1.1, hz2.2]
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  calc (1 : ENNReal) = ∫⁻ s in Set.Iic T, F (Set.Ioi (T - s)) ∂(U F) :=
        (inspection F hF T hT).symm
    _ ≤ ∫⁻ s in ⋃ j, I j, F (Set.Ioi (T - s)) ∂(U F) := lintegral_mono_set hcov
    _ = ∑' j, ∫⁻ s in I j, F (Set.Ioi (T - s)) ∂(U F) :=
        lintegral_iUnion (fun j => measurableSet_Ioc) hdisj _
    _ ≤ ∑' j : ℕ, F (Set.Ioi ((j : ℝ) * g)) * W F g (T - ((j : ℝ) + 1) * g) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        calc ∫⁻ s in I j, F (Set.Ioi (T - s)) ∂(U F)
            ≤ ∫⁻ _ in I j, F (Set.Ioi ((j : ℝ) * g)) ∂(U F) :=
              setLIntegral_mono' measurableSet_Ioc (fun s hs => measure_mono
                (Set.Ioi_subset_Ioi (by simp only [hI, Set.mem_Ioc] at hs; linarith [hs.2])))
          _ = F (Set.Ioi ((j : ℝ) * g)) * W F g (T - ((j : ℝ) + 1) * g) := by
              rw [setLIntegral_const, W]
              have he : T - ((j : ℝ) + 1) * g + g = T - (j : ℝ) * g := by ring
              rw [he]

/-- `Σ_j g·(1 − F((j+1)g)) ≤ μ`. -/
lemma tsum_tail_le_mean (F : Measure ℝ) (hF : IsCycleLaw F) (g : ℝ) (hg : 0 < g) :
    ∑' j : ℕ, ENNReal.ofReal g * F (Set.Ioi (((j : ℝ) + 1) * g)) ≤ mean F := by
  set I : ℕ → Set ℝ := fun j => Set.Ioc ((j : ℝ) * g) (((j : ℝ) + 1) * g) with hI
  have hdisj : Pairwise (Function.onFun Disjoint I) := by
    have key : ∀ i j : ℕ, i < j → Disjoint (I i) (I j) := by
      intro i j hij
      have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      refine Set.disjoint_left.mpr (fun z hz1 hz2 => ?_)
      simp only [hI, Set.mem_Ioc] at hz1 hz2
      nlinarith [hz1.2, hz2.1]
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hsub : (⋃ j, I j) ⊆ Set.Ioi 0 := by
    refine Set.iUnion_subset fun j z hz => ?_
    simp only [hI, Set.mem_Ioc] at hz
    simp only [Set.mem_Ioi]
    nlinarith [hz.1, (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  rw [mean_eq F hF]
  calc ∑' j : ℕ, ENNReal.ofReal g * F (Set.Ioi (((j : ℝ) + 1) * g))
      ≤ ∑' j, ∫⁻ u in I j, F (Set.Ioi u) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        calc ENNReal.ofReal g * F (Set.Ioi (((j : ℝ) + 1) * g))
            = ∫⁻ _ in I j, F (Set.Ioi (((j : ℝ) + 1) * g)) := by
              rw [setLIntegral_const, hI, Real.volume_Ioc, mul_comm]; congr 2; ring
          _ ≤ ∫⁻ u in I j, F (Set.Ioi u) :=
              setLIntegral_mono' measurableSet_Ioc (fun u hu => measure_mono
                (Set.Ioi_subset_Ioi (by simp only [hI, Set.mem_Ioc] at hu; exact hu.2)))
    _ = ∫⁻ u in ⋃ j, I j, F (Set.Ioi u) :=
        (lintegral_iUnion (fun j => measurableSet_Ioc) hdisj _).symm
    _ ≤ ∫⁻ u in Set.Ioi 0, F (Set.Ioi u) := lintegral_mono_set hsub


/-! ## D5: Blackwell lower bound -/

lemma tsum_Ioi_ne_top (F : Measure ℝ) (hF : IsCycleLaw F) (hμ : mean F ≠ ⊤) (g : ℝ)
    (hg : 0 < g) : ∑' j : ℕ, F (Set.Ioi ((j : ℝ) * g)) ≠ ⊤ := by
  have hP := hF.1
  have h1 := tsum_tail_le_mean F hF g hg
  rw [ENNReal.tsum_mul_left] at h1
  have hg' : ENNReal.ofReal g ≠ 0 := by simpa using hg
  have h2 : ∑' j : ℕ, F (Set.Ioi (((j : ℝ) + 1) * g)) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hg'] at h1
    exact hμ (top_le_iff.mp h1)
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ?_⟩
  simpa [Nat.cast_add, Nat.cast_one] using h2

lemma sum_Ioi_le (F : Measure ℝ) (hF : IsCycleLaw F) (hμ : mean F ≠ ⊤) (g : ℝ)
    (hg : 0 < g) (J : ℕ) :
    ∑ j ∈ Finset.range J, (F (Set.Ioi ((j : ℝ) * g))).toReal ≤ 1 + (mean F).toReal / g := by
  have hP := hF.1
  have h1 := tsum_tail_le_mean F hF g hg
  have hfin : ∀ j : ℕ, (F (Set.Ioi (((j : ℝ) + 1) * g))) ≠ ⊤ := fun j => measure_ne_top _ _
  have hpart : ∑ j ∈ Finset.range J, ENNReal.ofReal g * F (Set.Ioi (((j : ℝ) + 1) * g)) ≤
      mean F := le_trans (ENNReal.sum_le_tsum _) h1
  have hpartR : ∑ j ∈ Finset.range J, g * (F (Set.Ioi (((j : ℝ) + 1) * g))).toReal ≤
      (mean F).toReal := by
    have := ENNReal.toReal_mono hμ hpart
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin j))]
      at this
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hg.le] using this
  have hpartR' : ∑ j ∈ Finset.range J, (F (Set.Ioi (((j : ℝ) + 1) * g))).toReal ≤
      (mean F).toReal / g := by
    rw [le_div_iff₀ hg, Finset.sum_mul]
    simpa [mul_comm] using hpartR
  cases J with
  | zero => simp; positivity
  | succ n =>
    rw [Finset.sum_range_succ']
    have h0 : (F (Set.Ioi (((0 : ℕ) : ℝ) * g))).toReal ≤ 1 := by
      have := prob_le_one (μ := F) (s := Set.Ioi (((0 : ℕ) : ℝ) * g))
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have hn : ∑ j ∈ Finset.range n, (F (Set.Ioi (((j + 1 : ℕ) : ℝ) * g))).toReal ≤
        (mean F).toReal / g := by
      have := hpartR'
      rw [Finset.sum_range_succ] at this
      have hnn : 0 ≤ (F (Set.Ioi (((n : ℝ) + 1) * g))).toReal := ENNReal.toReal_nonneg
      push_cast
      linarith
    push_cast at hn h0 ⊢
    linarith

set_option maxHeartbeats 1000000 in
/-- Lower bound for windows `h` with `F (h, ∞) > 0`. -/
lemma fw_lower_small (F : Measure ℝ) (hF : IsCycleLaw F) (hper : IsAperiodic F)
    (hμ : mean F ≠ ⊤) (h : ℝ) (hh : 0 < h) (hpos : 0 < F (Set.Ioi h)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t in atTop, h * (mean F)⁻¹.toReal - δ ≤ fw F h t := by
  have hP := hF.1
  set μr := (mean F).toReal with hμr
  have hμpos : 0 < μr := ENNReal.toReal_pos (mean_pos F hF).ne' hμ
  have hinv : (mean F)⁻¹.toReal = μr⁻¹ := ENNReal.toReal_inv _
  rw [hinv]
  set a := (F (Set.Ioi h)).toReal with ha
  have hapos : 0 < a := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  -- choose k
  obtain ⟨k, hk⟩ := exists_nat_gt (4 * h / (μr * a * δ))
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  have hk1 : 1 ≤ k := by exact_mod_cast hkpos
  set g := h / k with hgdef
  have hg : 0 < g := div_pos hh hkpos
  have hkg : (k : ℝ) * g = h := by rw [hgdef]; field_simp
  have hgsmall : g * μr⁻¹ < a * δ / 4 := by
    rw [hgdef, div_mul_eq_mul_div, div_lt_iff₀ hkpos]
    rw [div_lt_iff₀ (by positivity)] at hk
    have : h * μr⁻¹ * 4 < a * δ * k * μr * μr⁻¹ := by
      field_simp; nlinarith [hk]
    field_simp at this ⊢; nlinarith [this]
  -- the upper-bound slack
  set ε := a * δ / (4 * (1 + μr / g)) with hεdef
  have hden : 0 < 1 + μr / g := by positivity
  have hε : 0 < ε := by positivity
  have hεS : ε * (1 + μr / g) = a * δ / 4 := by rw [hεdef]; field_simp
  -- the tail
  obtain ⟨C, hC0, hC⟩ := W_bdd F hF g hg.le
  set η := a * δ / (4 * (C + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hCη : C * η ≤ a * δ / 4 := by
    rw [hηdef]; rw [mul_div_assoc']; rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hapos hδ]
  have htail := ENNReal.tendsto_sum_nat_add (fun j : ℕ => F (Set.Ioi ((j : ℝ) * g)))
    (tsum_Ioi_ne_top F hF hμ g hg)
  have hev := (ENNReal.tendsto_nhds_zero.1 htail) (ENNReal.ofReal η) (by simpa using hη)
  obtain ⟨J0, hJ0⟩ := eventually_atTop.1 hev
  set J := max J0 k with hJ
  have hJk : k ≤ J := le_max_right _ _
  have hJtail : ∑' j : ℕ, F (Set.Ioi (((j + J : ℕ) : ℝ) * g)) ≤ ENNReal.ofReal η :=
    hJ0 J (le_max_left _ _)
  -- eventual upper bounds on the J windows
  have hup : ∀ᶠ T in atTop, ∀ j ∈ Finset.range J,
      fw F g (T - ((j : ℝ) + 1) * g) ≤ g * μr⁻¹ + ε := by
    rw [eventually_all_finset]
    intro j _
    have := fw_upper F hF hper g hg ε hε
    rw [hinv] at this
    exact (tendsto_atTop_add_const_right atTop (-(((j : ℝ) + 1) * g)) tendsto_id).eventually
      this |>.mono fun T hT => by simpa [sub_eq_add_neg] using hT
  have hmain : ∀ᶠ T in atTop, h * μr⁻¹ - δ ≤ fw F h (T - h) := by
    filter_upwards [hup, eventually_ge_atTop (0 : ℝ)] with T hT hT0
    set w : ℕ → ℝ := fun j => fw F g (T - ((j : ℝ) + 1) * g) with hw
    set b : ℕ → ℝ := fun j => (F (Set.Ioi ((j : ℝ) * g))).toReal with hb
    have hb0 : ∀ j, 0 ≤ b j := fun j => ENNReal.toReal_nonneg
    have hw0 : ∀ j, 0 ≤ w j := fun j => fw_nonneg F g _
    have hbk : b k = a := by simp only [hb, hkg, ha]
    have hbmono : ∀ j, j ≤ k → a ≤ b j := by
      intro j hj
      rw [← hbk]
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi ?_))
      have : (j : ℝ) ≤ k := by exact_mod_cast hj
      nlinarith
    -- inspection
    have hins := inspection_le_sum F hF T g hT0 hg
    rw [← Summable.sum_add_tsum_nat_add' (k := J) ENNReal.summable] at hins
    have htailW : ∑' j : ℕ, F (Set.Ioi (((j + J : ℕ) : ℝ) * g)) *
        W F g (T - (((j + J : ℕ) : ℝ) + 1) * g) ≤ ENNReal.ofReal η * ENNReal.ofReal C := by
      calc ∑' j : ℕ, F (Set.Ioi (((j + J : ℕ) : ℝ) * g)) *
            W F g (T - (((j + J : ℕ) : ℝ) + 1) * g)
          ≤ ∑' j : ℕ, F (Set.Ioi (((j + J : ℕ) : ℝ) * g)) * ENNReal.ofReal C := by
            refine ENNReal.tsum_le_tsum fun j => ?_
            have := hC (T - (((j + J : ℕ) : ℝ) + 1) * g)
            gcongr
            rw [← ENNReal.ofReal_toReal this.1]
            exact ENNReal.ofReal_le_ofReal this.2
        _ = (∑' j : ℕ, F (Set.Ioi (((j + J : ℕ) : ℝ) * g))) * ENNReal.ofReal C :=
            ENNReal.tsum_mul_right
        _ ≤ ENNReal.ofReal η * ENNReal.ofReal C := by gcongr
    have hfinsum : ∑ j ∈ Finset.range J, F (Set.Ioi ((j : ℝ) * g)) *
        W F g (T - ((j : ℝ) + 1) * g) = ENNReal.ofReal (∑ j ∈ Finset.range J, b j * w j) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hb0 j) (hw0 j))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ENNReal.ofReal_mul (hb0 j)]
      simp only [hb, hw, fw]
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (hC _).1]
    rw [hfinsum] at hins
    have hins' : 1 ≤ ∑ j ∈ Finset.range J, b j * w j + η * C := by
      have := le_trans hins (add_le_add le_rfl (htailW.trans_eq (ENNReal.ofReal_mul hη.le).symm))
      rw [← ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => mul_nonneg (hb0 j) (hw0 j))
        (mul_nonneg hη.le hC0), ← ENNReal.ofReal_one] at this
      exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (Finset.sum_nonneg fun j _ =>
        mul_nonneg (hb0 j) (hw0 j)) (mul_nonneg hη.le hC0))).1 this
    -- the window of length h
    have hWh : fw F h (T - h) = ∑ j ∈ Finset.range k, w j := by
      have hadd := W_add F g (T - h) hg.le k
      rw [hkg] at hadd
      rw [fw, hadd, ENNReal.toReal_sum (fun i _ => (hC _).1)]
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk := Finset.mem_range.1 hj
      simp only [hw, fw]
      congr 2
      rw [Nat.cast_sub (by omega), Nat.cast_sub hk1, ← hkg]; push_cast; ring
    -- algebra
    have hsplit := Finset.sum_range_add_sum_Ico (fun j => b j * w j) hJk
    have hsplitb := Finset.sum_range_add_sum_Ico b hJk
    have hlow : ∑ j ∈ Finset.range k, b j * w j ≤
        ∑ j ∈ Finset.range k, (b j - a) * (g * μr⁻¹ + ε) + a * fw F h (T - h) := by
      rw [hWh, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk := Finset.mem_range.1 hj
      have h1 : b j * w j = (b j - a) * w j + a * w j := by ring
      rw [h1]
      have := hT j (Finset.mem_range.2 (lt_of_lt_of_le hjk hJk))
      have hba : 0 ≤ b j - a := by linarith [hbmono j hjk.le]
      nlinarith [mul_le_mul_of_nonneg_left this hba]
    have hhigh : ∑ j ∈ Finset.Ico k J, b j * w j ≤
        ∑ j ∈ Finset.Ico k J, b j * (g * μr⁻¹ + ε) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjJ := (Finset.mem_Ico.1 hj).2
      exact mul_le_mul_of_nonneg_left (hT j (Finset.mem_range.2 hjJ)) (hb0 j)
    have hsumb := sum_Ioi_le F hF hμ g hg J
    have hsub : ∑ j ∈ Finset.range k, (b j - a) * (g * μr⁻¹ + ε) =
        (∑ j ∈ Finset.range k, b j) * (g * μr⁻¹ + ε) - (k : ℝ) * a * (g * μr⁻¹ + ε) := by
      rw [Finset.sum_mul]
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      ring
    have hIco : ∑ j ∈ Finset.Ico k J, b j * (g * μr⁻¹ + ε) =
        (∑ j ∈ Finset.Ico k J, b j) * (g * μr⁻¹ + ε) := by rw [Finset.sum_mul]
    -- total: 1 ≤ (S_J)(c+ε) - k a (c + ε) + a fw + η C
    set S := ∑ j ∈ Finset.range J, b j with hS
    have htot : 1 ≤ S * (g * μr⁻¹ + ε) - (k : ℝ) * a * (g * μr⁻¹ + ε) +
        a * fw F h (T - h) + η * C := by
      have e1 : S = ∑ j ∈ Finset.range k, b j + ∑ j ∈ Finset.Ico k J, b j := hsplitb.symm
      have e2 : ∑ j ∈ Finset.range J, b j * w j =
          ∑ j ∈ Finset.range k, b j * w j + ∑ j ∈ Finset.Ico k J, b j * w j := hsplit.symm
      rw [e1]; linarith
    have hcS : S * (g * μr⁻¹) ≤ g * μr⁻¹ + 1 := by
      have : S * (g * μr⁻¹) ≤ (1 + μr / g) * (g * μr⁻¹) :=
        mul_le_mul_of_nonneg_right hsumb (by positivity)
      have e : (1 + μr / g) * (g * μr⁻¹) = g * μr⁻¹ + 1 := by field_simp
      linarith
    have hεS' : S * ε ≤ a * δ / 4 := by
      rw [← hεS]; rw [mul_comm S ε]; exact mul_le_mul_of_nonneg_left hsumb hε.le
    have hka : (k : ℝ) * a * (g * μr⁻¹ + ε) ≥ h * μr⁻¹ * a := by
      have : (k : ℝ) * a * (g * μr⁻¹) = h * μr⁻¹ * a := by rw [← hkg]; ring
      have e3 : (k : ℝ) * a * (g * μr⁻¹ + ε) = (k : ℝ) * a * (g * μr⁻¹) + (k : ℝ) * a * ε := by
        ring
      have := mul_pos (mul_pos hkpos hapos) hε
      linarith
    have hfin : a * (h * μr⁻¹ - fw F h (T - h)) < a * δ := by
      have : η * C ≤ a * δ / 4 := by linarith [hCη, mul_comm η C]
      have e1 : S * (g * μr⁻¹ + ε) = S * (g * μr⁻¹) + S * ε := by ring
      have e2 : a * (h * μr⁻¹ - fw F h (T - h)) = h * μr⁻¹ * a - a * fw F h (T - h) := by ring
      have := mul_pos hapos hδ
      rw [e2]
      linarith
    have := lt_of_mul_lt_mul_left hfin hapos.le
    linarith
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 hmain
  refine eventually_atTop.2 ⟨T0, fun t ht => ?_⟩
  have := hT0 (t + h) (by linarith)
  simpa using this

/-- **Blackwell lower bound.** -/
lemma fw_lower (F : Measure ℝ) (hF : IsCycleLaw F) (hper : IsAperiodic F)
    (hμ : mean F ≠ ⊤) (h : ℝ) (hh : 0 < h) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t in atTop, h * (mean F)⁻¹.toReal - δ ≤ fw F h t := by
  have hP := hF.1
  obtain ⟨u0, hu0, hpos⟩ := exists_tail_pos F hF
  obtain ⟨M, hM⟩ := exists_nat_gt (h / u0)
  have hMpos : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
  set h' := h / M with hh'
  have hh'pos : 0 < h' := div_pos hh hMpos
  have hMh : (M : ℝ) * h' = h := by rw [hh']; field_simp
  have hh'le : h' ≤ u0 := by
    rw [hh', div_le_iff₀ hMpos]; rw [div_lt_iff₀ hu0] at hM; linarith
  have hpos' : 0 < F (Set.Ioi h') := lt_of_lt_of_le hpos (measure_mono (Set.Ioi_subset_Ioi hh'le))
  obtain ⟨C, -, hC⟩ := W_bdd F hF h' hh'pos.le
  have hev : ∀ᶠ t in atTop, ∀ i ∈ Finset.range M,
      h' * (mean F)⁻¹.toReal - δ / M ≤ fw F h' (t + i * h') := by
    rw [eventually_all_finset]
    intro i _
    exact (tendsto_atTop_add_const_right atTop ((i : ℝ) * h') tendsto_id).eventually
      (fw_lower_small F hF hper hμ h' hh'pos hpos' (δ / M) (div_pos hδ hMpos))
  filter_upwards [hev] with t ht
  have hsum : fw F h t = ∑ i ∈ Finset.range M, fw F h' (t + i * h') := by
    rw [fw, ← hMh, W_add F h' t hh'pos.le M, ENNReal.toReal_sum (fun i _ => (hC _).1)]; rfl
  rw [hsum]
  have := Finset.sum_le_sum ht
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have e : (M : ℝ) * (h' * (mean F)⁻¹.toReal - δ / M) = h * (mean F)⁻¹.toReal - δ := by
    rw [← hMh]; field_simp
  linarith

/-- **Blackwell's renewal theorem** (both `μ < ∞` and `μ = ∞`). -/
theorem blackwell (F : Measure ℝ) (hF : IsCycleLaw F) (hper : IsAperiodic F) (h : ℝ)
    (hh : 0 < h) : Tendsto (fw F h) atTop (𝓝 (h * (mean F)⁻¹.toReal)) := by
  rw [tendsto_order]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_cases hμ : mean F = ⊤
    · have : h * (mean F)⁻¹.toReal = 0 := by simp [hμ]
      rw [this] at hx
      exact Eventually.of_forall fun t => lt_of_lt_of_le hx (fw_nonneg F h t)
    · filter_upwards [fw_lower F hF hper hμ h hh ((h * (mean F)⁻¹.toReal - x) / 2)
        (by linarith)] with t ht
      linarith
  · filter_upwards [fw_upper F hF hper h hh ((x - h * (mean F)⁻¹.toReal) / 2)
      (by linarith)] with t ht
    linarith


/-! ## E: key renewal theorem for monotone `Ψ`, for an abstract renewal-type measure -/

lemma psi_nonneg (Ψ : ℝ → ℝ) (hmono : AntitoneOn Ψ (Set.Ioi 0))
    (hint : IntegrableOn Ψ (Set.Ioi 0)) (v : ℝ) (hv : 0 < v) : 0 ≤ Ψ v := by
  by_contra hneg
  rw [not_le] at hneg
  set δ := -Ψ v with hδ
  have hδpos : 0 < δ := by linarith
  have hfin := Integrable.measure_norm_ge_lt_top hint hδpos
  have hsub : Set.Ioi v ⊆ {x | δ ≤ ‖Ψ x‖} := by
    intro x hx
    have hx' : v ≤ x := le_of_lt hx
    have := hmono (Set.mem_Ioi.2 hv) (Set.mem_Ioi.2 (lt_trans hv hx)) hx'
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
    rw [abs_of_neg (by linarith)]; linarith
  have htop : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi v) = ⊤ := by
    rw [Measure.restrict_apply measurableSet_Ioi, Set.Ioi_inter_Ioi, sup_of_le_left hv.le]
    exact Real.volume_Ioi
  have := lt_of_le_of_lt (measure_mono hsub) hfin
  rw [htop] at this
  exact lt_irrefl _ this

lemma iUnion_windows (t h : ℝ) (hh : 0 < h) :
    (⋃ j : ℕ, Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h)) = Set.Iic t := by
  ext s
  constructor
  · intro hs
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hs
    simp only [Set.mem_Ioc] at hj
    simp only [Set.mem_Iic]
    nlinarith [hj.2, (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  · intro hs
    simp only [Set.mem_Iic] at hs
    have hq : 0 ≤ (t - s) / h := div_nonneg (by linarith) hh.le
    refine Set.mem_iUnion.mpr ⟨⌊(t - s) / h⌋₊, ?_⟩
    have h1 := Nat.floor_le hq
    have h2 := Nat.lt_floor_add_one ((t - s) / h)
    rw [le_div_iff₀ hh] at h1
    rw [div_lt_iff₀ hh] at h2
    simp only [Set.mem_Ioc]
    constructor <;> linarith

lemma disjoint_windows (t h : ℝ) (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint
      (fun j : ℕ => Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h))) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (Set.Ioc (t - ((i : ℝ) + 1) * h) (t - (i : ℝ) * h))
      (Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h)) := by
    intro i j hij
    have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    refine Set.disjoint_left.mpr (fun z hz1 hz2 => ?_)
    simp only [Set.mem_Ioc] at hz1 hz2
    nlinarith [hz1.1, hz2.2]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact key i j h'
  · exact (key j i h').symm

lemma iUnion_Ioc_mul (h : ℝ) (hh : 0 < h) :
    (⋃ i : ℕ, Set.Ioc ((i : ℝ) * h) ((i : ℝ) * h + h)) = Set.Ioi 0 := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    simp only [Set.mem_Ioc] at hi
    simp only [Set.mem_Ioi]
    nlinarith [hi.1, (Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  · intro hz
    simp only [Set.mem_Ioi] at hz
    have hq : 0 < z / h := div_pos hz hh
    set n := ⌈z / h⌉₊ with hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hq))
    refine Set.mem_iUnion.mpr ⟨n - 1, ?_⟩
    have h1 := Nat.le_ceil (z / h)
    have h2 := Nat.ceil_lt_add_one hq.le
    rw [← hn] at h1 h2
    rw [div_le_iff₀ hh] at h1
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hh] at h2
    simp only [Set.mem_Ioc]
    rw [Nat.cast_sub hn1]
    push_cast
    constructor <;> nlinarith

lemma disjoint_Ioc_mul (h : ℝ) (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint (fun i : ℕ => Set.Ioc ((i : ℝ) * h) ((i : ℝ) * h + h))) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (Set.Ioc ((i : ℝ) * h) ((i : ℝ) * h + h))
      (Set.Ioc ((j : ℝ) * h) ((j : ℝ) * h + h)) := by
    intro i j hij
    have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    refine Set.disjoint_left.mpr (fun z hz1 hz2 => ?_)
    simp only [Set.mem_Ioc] at hz1 hz2
    nlinarith [hz1.2, hz2.1]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact key i j h'
  · exact (key j i h').symm

lemma setIntegral_const_Ioc (a h k : ℝ) (hh : 0 ≤ h) : ∫ _ in Set.Ioc a (a + h), k = h * k := by
  rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

lemma p_ge (Ψ : ℝ → ℝ) (hmono : AntitoneOn Ψ (Set.Ioi 0)) (hint : IntegrableOn Ψ (Set.Ioi 0))
    (h : ℝ) (hh : 0 < h) (a : ℝ) (ha : 0 ≤ a) (u : ℝ) (hu : a + h ≤ u) :
    h * Ψ u ≤ ∫ v in Set.Ioc a (a + h), Ψ v := by
  rw [← setIntegral_const_Ioc a h (Ψ u) hh.le]
  refine setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioc]))
    (hint.mono_set fun v hv => lt_of_le_of_lt ha hv.1) measurableSet_Ioc (fun v hv => ?_)
  exact hmono (lt_of_le_of_lt ha hv.1) (show (0:ℝ) < u by linarith) (le_trans hv.2 hu)

lemma p_le (Ψ : ℝ → ℝ) (hmono : AntitoneOn Ψ (Set.Ioi 0)) (hint : IntegrableOn Ψ (Set.Ioi 0))
    (h : ℝ) (hh : 0 < h) (a : ℝ) (u : ℝ) (hu0 : 0 < u) (hu : u ≤ a) :
    ∫ v in Set.Ioc a (a + h), Ψ v ≤ h * Ψ u := by
  rw [← setIntegral_const_Ioc a h (Ψ u) hh.le]
  refine setIntegral_mono_on (hint.mono_set fun v hv => lt_of_lt_of_le hu0 (le_trans hu hv.1.le))
    (integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc (fun v hv => ?_)
  exact hmono hu0 (lt_of_lt_of_le hu0 (le_trans hu hv.1.le)) (le_trans hu hv.1.le)

/-- The integral over `[0,t]` splits into the windows `(t-(j+1)h, t-jh]`. -/
lemma window_hasSum (H : Measure ℝ) (hneg : H (Set.Iio 0) = 0)
    (hfin : ∀ a b : ℝ, H (Set.Ioc a b) ≠ ⊤) (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) (C0 : ℝ)
    (hC0 : ∀ v : ℝ, 0 ≤ v → |Ψ v| ≤ C0) (t : ℝ) (h : ℝ) (hh : 0 < h) :
    HasSum (fun j : ℕ => ∫ s in Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h), Ψ (t - s) ∂H)
      (∫ s in Set.Icc 0 t, Ψ (t - s) ∂H) ∧
    IntegrableOn (fun s => Ψ (t - s)) (Set.Iic t) H := by
  have hae : (Set.Icc 0 t : Set ℝ) =ᵐ[H] Set.Iic t := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [Set.diff_eq_empty.2 (fun s hs => Set.mem_Iic.2 hs.2)]; exact measure_empty
    · refine measure_mono_null (fun s hs => ?_) hneg
      simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Icc, not_and, not_le] at hs
      simp only [Set.mem_Iio]
      by_contra hc; rw [not_lt] at hc; exact absurd (hs.2 hc) (not_lt.2 hs.1)
  have hfinI : H (Set.Iic t) ≠ ⊤ := by
    have hsub : Set.Iic t ⊆ Set.Iio 0 ∪ Set.Ioc (min (-1) t - 1) t := by
      intro s hs
      simp only [Set.mem_Iic] at hs
      by_cases h0 : s < 0
      · exact Or.inl h0
      · refine Or.inr ⟨?_, hs⟩
        have := min_le_left (-1 : ℝ) t
        linarith [not_lt.1 h0]
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (measure_union_le _ _))
    rw [hneg, zero_add]; exact hfin _ _
  have hint : IntegrableOn (fun s => Ψ (t - s)) (Set.Iic t) H := by
    refine Measure.integrableOn_of_bounded hfinI
      ((hΨm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) (M := C0) ?_
    refine ae_restrict_of_forall_mem measurableSet_Iic fun s hs => ?_
    simp only [Real.norm_eq_abs, Function.comp]
    exact hC0 _ (by simp only [Set.mem_Iic] at hs; linarith)
  refine ⟨?_, hint⟩
  rw [setIntegral_congr_set hae, ← iUnion_windows t h hh]
  refine hasSum_integral_iUnion (fun j => measurableSet_Ioc) (disjoint_windows t h hh) ?_
  rw [iUnion_windows t h hh]; exact hint

/-- **Key renewal theorem** (monotone `Ψ`) for any measure with Blackwell asymptotics. -/
theorem krt_abstract (H : Measure ℝ) (c : ℝ) (hc : 0 ≤ c) (hneg : H (Set.Iio 0) = 0)
    (hfin : ∀ a b : ℝ, H (Set.Ioc a b) ≠ ⊤)
    (hbdd : ∀ h > 0, ∃ C : ℝ, ∀ t, (H (Set.Ioc t (t + h))).toReal ≤ C)
    (hbw : ∀ h > 0, Tendsto (fun t => (H (Set.Ioc t (t + h))).toReal) atTop (𝓝 (c * h)))
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) (hbddΨ : ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → |Ψ v| ≤ C)
    (hmono : AntitoneOn Ψ (Set.Ioi 0)) (hint : IntegrableOn Ψ (Set.Ioi 0)) :
    Tendsto (fun t => ∫ s in Set.Icc 0 t, Ψ (t - s) ∂H) atTop
      (𝓝 (c * ∫ v in Set.Ioi 0, Ψ v)) := by
  obtain ⟨C0, hC0⟩ := hbddΨ
  have hC0nn : 0 ≤ C0 := le_trans (abs_nonneg _) (hC0 0 le_rfl)
  set I := ∫ v in Set.Ioi 0, Ψ v with hI
  set G := fun t => ∫ s in Set.Icc 0 t, Ψ (t - s) ∂H with hG
  have key : ∀ h > 0, ∀ᶠ t in atTop,
      G t ≤ c * I + c * h * C0 + h ∧ c * I - 3 * (c * h * C0) - h ≤ G t := by
    intro h hh
    obtain ⟨Ch, hCh⟩ := hbdd h hh
    set p : ℕ → ℝ := fun i => ∫ v in Set.Ioc ((i : ℝ) * h) ((i : ℝ) * h + h), Ψ v with hp
    have hpI : HasSum p I := by
      have := hasSum_integral_iUnion (fun i => measurableSet_Ioc) (disjoint_Ioc_mul h hh)
        (by rw [iUnion_Ioc_mul h hh]; exact hint)
      rwa [iUnion_Ioc_mul h hh] at this
    have hpC : ∀ i, p i ≤ h * C0 := by
      intro i
      simp only [hp]
      rw [← setIntegral_const_Ioc _ h C0 hh.le]
      refine setIntegral_mono_on (hint.mono_set fun v hv => ?_)
        (integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc (fun v hv => ?_)
      · exact lt_of_le_of_lt (by positivity) hv.1
      · exact le_trans (le_abs_self _) (hC0 v (le_trans (by positivity) hv.1.le))
    set B : ℕ → ℝ := fun j => if j = 0 then C0 else p (j - 1) / h with hB
    set A : ℕ → ℝ := fun j => if j = 0 then -C0 else p (j + 1) / h with hA
    have hBs : Summable B := by
      refine (summable_nat_add_iff 1).1 ?_
      simpa [hB] using hpI.summable.div_const h
    have hAs : Summable A := by
      refine (summable_nat_add_iff 1).1 ?_
      have := ((summable_nat_add_iff 2).2 hpI.summable).div_const h
      simpa [hA] using this
    set w : ℕ → ℝ → ℝ := fun j t =>
      (H (Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h))).toReal with hw
    have hwshift : ∀ j t, w j t = (H (Set.Ioc (t - ((j : ℝ) + 1) * h)
        (t - ((j : ℝ) + 1) * h + h))).toReal := by
      intro j t; simp only [hw]; congr 3; ring
    have hw0 : ∀ j t, 0 ≤ w j t := fun j t => ENNReal.toReal_nonneg
    have hwC : ∀ j t, w j t ≤ Ch := fun j t => by rw [hwshift]; exact hCh _
    have hwlim : ∀ j, Tendsto (w j) atTop (𝓝 (c * h)) := by
      intro j
      have := (hbw h hh).comp (tendsto_atTop_add_const_right atTop (-(((j : ℝ) + 1) * h))
        tendsto_id)
      refine this.congr fun t => ?_
      rw [hwshift]; simp only [Function.comp, id, sub_eq_add_neg]
    -- the two comparison series
    have hupper_lim : Tendsto (fun t => ∑' j, B j * w j t) atTop (𝓝 (∑' j, B j * (c * h))) :=
      tendsto_tsum_of_dominated_convergence (bound := fun j => |B j| * Ch)
        (hBs.abs.mul_right Ch) (fun j => (hwlim j).const_mul (B j))
        (Eventually.of_forall fun t j => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 j t)]
          exact mul_le_mul_of_nonneg_left (hwC j t) (abs_nonneg _))
    have hlower_lim : Tendsto (fun t => ∑' j, A j * w j t) atTop (𝓝 (∑' j, A j * (c * h))) :=
      tendsto_tsum_of_dominated_convergence (bound := fun j => |A j| * Ch)
        (hAs.abs.mul_right Ch) (fun j => (hwlim j).const_mul (A j))
        (Eventually.of_forall fun t j => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 j t)]
          exact mul_le_mul_of_nonneg_left (hwC j t) (abs_nonneg _))
    have hBval : ∑' j, B j * (c * h) = c * h * C0 + c * I := by
      rw [tsum_mul_right, hBs.tsum_eq_zero_add]
      have : ∑' j, B (j + 1) = I / h := by
        simp only [hB, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        rw [tsum_div_const, hpI.tsum_eq]
      rw [this]; simp only [hB, if_true]; field_simp
    have hAval : c * I - 3 * (c * h * C0) ≤ ∑' j, A j * (c * h) := by
      rw [tsum_mul_right, hAs.tsum_eq_zero_add]
      have h2 : ∑' j, A (j + 1) = (∑' i, p (i + 2)) / h := by
        simp only [hA, Nat.add_one_ne_zero, if_false]
        rw [tsum_div_const]
      have h3 : ∑' i, p (i + 2) = I - p 0 - p 1 := by
        have := (((summable_nat_add_iff 2).2 hpI.summable).sum_add_tsum_nat_add'
          (k := 2) (f := p))
        rw [hpI.tsum_eq, Finset.sum_range_succ, Finset.sum_range_one] at this
        linarith
      rw [h2, h3]; simp only [hA, if_true]
      have e : (-C0 + (I - p 0 - p 1) / h) * (c * h) = c * I - c * h * C0 - c * (p 0 + p 1) := by
        field_simp; ring
      rw [e]
      have := hpC 0; have := hpC 1
      have : c * (p 0 + p 1) ≤ c * (2 * (h * C0)) := mul_le_mul_of_nonneg_left (by linarith) hc
      nlinarith
    -- comparison of G with the two series
    have hcomp : ∀ t, ∑' j, A j * w j t ≤ G t ∧ G t ≤ ∑' j, B j * w j t := by
      intro t
      obtain ⟨hsum, hintI⟩ := window_hasSum H hneg hfin Ψ hΨm C0 hC0 t h hh
      have hVsub : ∀ j : ℕ, Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h) ⊆ Set.Iic t :=
        fun j s hs => Set.mem_Iic.2 (by
          have := hs.2; nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
      have hVfin : ∀ j : ℕ, H (Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h)) ≠ ⊤ :=
        fun j => hfin _ _
      have hu : ∀ j : ℕ, ∀ s ∈ Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h),
          (j : ℝ) * h ≤ t - s ∧ t - s < ((j : ℝ) + 1) * h := by
        intro j s hs; simp only [Set.mem_Ioc] at hs; constructor <;> linarith [hs.1, hs.2]
      have hgB : ∀ j : ℕ, ∫ s in Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h), Ψ (t - s) ∂H
          ≤ B j * w j t := by
        intro j
        have hconst : ∫ _ in Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h), B j ∂H =
            B j * w j t := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
        rw [← hconst]
        refine setIntegral_mono_on (hintI.mono_set (hVsub j)) (integrableOn_const (hVfin j))
          measurableSet_Ioc (fun s hs => ?_)
        obtain ⟨hu1, hu2⟩ := hu j s hs
        rcases j with _ | i
        · simp only [hB, if_true]
          exact le_trans (le_abs_self _) (hC0 _ (by simpa using hu1))
        · simp only [hB, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          rw [le_div_iff₀ hh, mul_comm]
          have := p_ge Ψ hmono hint h hh ((i : ℝ) * h) (by positivity) (t - s)
            (by push_cast at hu1; linarith)
          simpa [hp] using this
      have hgA : ∀ j : ℕ, A j * w j t ≤
          ∫ s in Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h), Ψ (t - s) ∂H := by
        intro j
        have hconst : ∫ _ in Set.Ioc (t - ((j : ℝ) + 1) * h) (t - (j : ℝ) * h), A j ∂H =
            A j * w j t := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
        rw [← hconst]
        refine setIntegral_mono_on (integrableOn_const (hVfin j)) (hintI.mono_set (hVsub j))
          measurableSet_Ioc (fun s hs => ?_)
        obtain ⟨hu1, hu2⟩ := hu j s hs
        rcases j with _ | i
        · simp only [hA, if_true]
          have := hC0 (t - s) (by simpa using hu1)
          linarith [neg_abs_le (Ψ (t - s))]
        · simp only [hA, Nat.add_one_ne_zero, if_false]
          rw [div_le_iff₀ hh, mul_comm]
          have hpos : 0 < t - s := lt_of_lt_of_le (by positivity) hu1
          have := p_le Ψ hmono hint h hh (((i + 1 + 1 : ℕ) : ℝ) * h) (t - s) hpos
            (by push_cast at hu2 ⊢; linarith)
          simpa [hp] using this
      have hBsum : Summable (fun j => B j * w j t) :=
        Summable.of_norm_bounded (hBs.abs.mul_right Ch) (fun j => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 j t)]
          exact mul_le_mul_of_nonneg_left (hwC j t) (abs_nonneg _))
      have hAsum : Summable (fun j => A j * w j t) :=
        Summable.of_norm_bounded (hAs.abs.mul_right Ch) (fun j => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 j t)]
          exact mul_le_mul_of_nonneg_left (hwC j t) (abs_nonneg _))
      exact ⟨hasSum_le hgA hAsum.hasSum hsum, hasSum_le hgB hsum hBsum.hasSum⟩
    have hev1 := (tendsto_order.1 hupper_lim).2 (c * h * C0 + c * I + h) (by rw [hBval]; linarith)
    have hev2 := (tendsto_order.1 hlower_lim).1 (c * I - 3 * (c * h * C0) - h) (by linarith)
    filter_upwards [hev1, hev2] with t ht1 ht2
    obtain ⟨hc1, hc2⟩ := hcomp t
    constructor <;> linarith
  rw [tendsto_order]
  have hgap : ∀ d > 0, ∃ h > 0, 3 * (c * h * C0) + h < d := by
    intro d hd
    refine ⟨d / (2 * (3 * c * C0 + 1)), by positivity, ?_⟩
    have hpos : 0 < 3 * c * C0 + 1 := by positivity
    have e : 3 * (c * (d / (2 * (3 * c * C0 + 1))) * C0) + d / (2 * (3 * c * C0 + 1)) = d / 2 := by
      field_simp
    linarith
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨h, hh, hgh⟩ := hgap (c * I - x) (by linarith)
    filter_upwards [key h hh] with t ht
    linarith [ht.2]
  · obtain ⟨h, hh, hgh⟩ := hgap (x - c * I) (by linarith)
    filter_upwards [key h hh] with t ht
    have : c * h * C0 ≥ 0 := by positivity
    linarith [ht.1]


/-! ## F: the delayed renewal measure `H_K = K ∗ U` -/

lemma renewal_eq_conv (F K : Measure ℝ) [IsProbabilityMeasure F] [SFinite K] :
    renewalMeasure K F = K ∗ U F := by
  have := U_sfinite F
  ext A hA
  have hm : Measurable (A.indicator (1 : ℝ → ENNReal)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    Measure.lintegral_conv hm, renewalMeasure, lintegral_sum_measure]
  simp only [lintegral_U]
  rw [lintegral_tsum (fun n => ?_)]
  · refine tsum_congr fun n => ?_
    have := convPow_isProb F n
    rw [Measure.lintegral_conv hm]
  · have := convPow_isProb F n
    exact (Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => A.indicator 1 (p.1 + p.2))
      (hm.comp measurable_add)).aemeasurable

lemma H_window (F K : Measure ℝ) [IsProbabilityMeasure F] [SFinite K] (t h : ℝ) :
    renewalMeasure K F (Set.Ioc t (t + h)) = ∫⁻ x, W F h (t - x) ∂K := by
  have := U_sfinite F
  rw [renewal_eq_conv, ← lintegral_indicator_one measurableSet_Ioc,
    Measure.lintegral_conv (measurable_one.indicator measurableSet_Ioc)]
  refine lintegral_congr fun x => ?_
  rw [W, ← lintegral_indicator_one measurableSet_Ioc]
  refine lintegral_congr fun y => ?_
  have hset : (t < x + y ∧ x + y ≤ t + h) ↔ (t - x < y ∧ y ≤ t - x + h) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [Set.indicator_apply, Set.mem_Ioc, Pi.one_apply, hset]

lemma H_neg (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K) [SFinite K] :
    renewalMeasure K F (Set.Iio 0) = 0 := by
  have hP := hF.1
  have := U_sfinite F
  rw [renewal_eq_conv, ← lintegral_indicator_one measurableSet_Iio,
    Measure.lintegral_conv (measurable_one.indicator measurableSet_Iio)]
  have hK0 : ∀ᵐ x ∂K, 0 ≤ x := by
    rw [ae_iff]; exact measure_mono_null (fun x hx => Set.mem_Iio.2 (not_le.1 hx)) hK.1
  have hU0 : ∀ᵐ y ∂(U F), 0 ≤ y := by
    rw [ae_iff]; exact measure_mono_null (fun x hx => Set.mem_Iio.2 (not_le.1 hx)) (U_Iio F hF.2.1)
  calc ∫⁻ x, ∫⁻ y, (Set.Iio 0).indicator 1 (x + y) ∂(U F) ∂K = ∫⁻ _, 0 ∂K := by
        refine lintegral_congr_ae (hK0.mono fun x hx => ?_)
        calc ∫⁻ y, (Set.Iio 0).indicator 1 (x + y) ∂(U F) = ∫⁻ _, 0 ∂(U F) := by
              refine lintegral_congr_ae (hU0.mono fun y hy => ?_)
              simp [Set.indicator_apply, not_lt.2 (add_nonneg hx hy)]
          _ = 0 := lintegral_zero
    _ = 0 := lintegral_zero

lemma H_window_le (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K) [SFinite K]
    (h : ℝ) (hh : 0 ≤ h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, renewalMeasure K F (Set.Ioc t (t + h)) ≤ ENNReal.ofReal C := by
  have hP := hF.1
  obtain ⟨C, hC0, hC⟩ := W_bdd F hF h hh
  refine ⟨C, hC0, fun t => ?_⟩
  rw [H_window]
  calc ∫⁻ x, W F h (t - x) ∂K ≤ ∫⁻ _, ENNReal.ofReal C ∂K := lintegral_mono fun x => by
        rw [← ENNReal.ofReal_toReal (hC _).1]; exact ENNReal.ofReal_le_ofReal (hC _).2
    _ = ENNReal.ofReal C * K Set.univ := lintegral_const _
    _ ≤ ENNReal.ofReal C * 1 := by gcongr; exact hK.2
    _ = ENNReal.ofReal C := mul_one _

lemma H_fin (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K) [SFinite K] (a b : ℝ) :
    renewalMeasure K F (Set.Ioc a b) ≠ ⊤ := by
  rcases le_or_gt a b with hab | hab
  · obtain ⟨C, -, hC⟩ := H_window_le F K hF hK (b - a) (by linarith)
    have e : Set.Ioc a b = Set.Ioc a (a + (b - a)) := by congr 1; ring
    rw [e]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC a)
  · rw [Set.Ioc_eq_empty (not_lt.2 hab.le)]; simp

lemma H_bdd (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K) [SFinite K] :
    ∀ h > 0, ∃ C : ℝ, ∀ t, (renewalMeasure K F (Set.Ioc t (t + h))).toReal ≤ C := by
  intro h hh
  obtain ⟨C, hC0, hC⟩ := H_window_le F K hF hK h hh.le
  exact ⟨C, fun t => ENNReal.toReal_le_of_le_ofReal hC0 (hC t)⟩

lemma H_blackwell (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K)
    (hper : IsAperiodic F) [IsFiniteMeasure K] :
    ∀ h > 0, Tendsto (fun t => (renewalMeasure K F (Set.Ioc t (t + h))).toReal) atTop
      (𝓝 ((K Set.univ).toReal * (mean F)⁻¹.toReal * h)) := by
  intro h hh
  have hP := hF.1
  obtain ⟨C, -, hC⟩ := W_bdd F hF h hh.le
  have hmeas : ∀ t, Measurable (fun x => W F h (t - x)) := fun t =>
    (measurable_W F h).comp (measurable_const.sub measurable_id)
  have eq : ∀ t, (renewalMeasure K F (Set.Ioc t (t + h))).toReal = ∫ x, fw F h (t - x) ∂K := by
    intro t
    rw [H_window, ← integral_toReal (hmeas t).aemeasurable
      (ae_of_all _ fun x => lt_top_iff_ne_top.2 (hC _).1)]
    rfl
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := K) (l := atTop)
    (F := fun t x => fw F h (t - x)) (f := fun _ => h * (mean F)⁻¹.toReal) (fun _ => C)
    (Eventually.of_forall fun t => (hmeas t).ennreal_toReal.aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fw_nonneg _ _ _)]; exact (hC _).2)
    (integrable_const C)
    (ae_of_all _ fun x => ((blackwell F hF hper h hh).comp
      (tendsto_atTop_add_const_right atTop (-x) tendsto_id)).congr fun t => by
        simp only [Function.comp, id, sub_eq_add_neg])
  rw [integral_const, smul_eq_mul, measureReal_def] at hlim
  refine (hlim.congr fun t => (eq t).symm).trans (le_of_eq ?_)
  congr 1; ring

end SmithRegenerative.Equilibrium.RenewalLib

namespace SmithRegenerative.Equilibrium.RenewalLib

open SmithRegenerative.Equilibrium

/-! ## G: spread-out laws — `U ≤ (finite) + D·Lebesgue` (for theorem_1, 7ef7cec6) -/

lemma ac_piece (G : Measure ℝ) [IsFiniteMeasure G] (hG : ¬ G.MutuallySingular volume) :
    ∃ (b : ℝ → ENNReal) (M : ℝ), Measurable b ∧ 0 < M ∧ (∀ x, b x ≤ ENNReal.ofReal M) ∧
      (∀ x, x ∉ Set.Icc (-M) M → b x = 0) ∧ volume.withDensity b ≤ G ∧ 0 < ∫⁻ x, b x := by
  set g := G.rnDeriv volume with hgdef
  have hg : Measurable g := Measure.measurable_rnDeriv _ _
  set bn : ℕ → ℝ → ENNReal := fun n => (Set.Icc (-((n:ℝ) + 1)) ((n:ℝ) + 1)).indicator
    (fun x => min (g x) (ENNReal.ofReal ((n:ℝ) + 1))) with hbn
  have hbn_m : ∀ n, Measurable (bn n) := fun n =>
    (hg.min measurable_const).indicator measurableSet_Icc
  have hex : ∃ n : ℕ, 0 < ∫⁻ x, bn n x := by
    by_contra hne
    push Not at hne
    have h0 : ∀ n, bn n =ᵐ[volume] 0 := fun n =>
      (lintegral_eq_zero_iff (hbn_m n)).1 (le_antisymm (hne n) bot_le)
    apply hG
    rw [← Measure.rnDeriv_eq_zero]
    filter_upwards [ae_all_iff.2 h0] with x hx
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    have hab := abs_le.1 hn
    have hmem : x ∈ Set.Icc (-((n:ℝ) + 1)) ((n:ℝ) + 1) := by
      constructor <;> linarith [hab.1, hab.2]
    have h1 := hx n
    simp only [hbn, Set.indicator_of_mem hmem, Pi.zero_apply] at h1
    have hpos : (0:ENNReal) < ENNReal.ofReal ((n:ℝ) + 1) := ENNReal.ofReal_pos.2 (by positivity)
    rcases min_choice (g x) (ENNReal.ofReal ((n:ℝ) + 1)) with h | h
    · rw [h] at h1; exact h1
    · rw [h] at h1; exact absurd h1 hpos.ne'
  obtain ⟨n, hn⟩ := hex
  refine ⟨bn n, (n:ℝ) + 1, hbn_m n, by positivity, fun x => ?_, fun x hx => ?_, ?_, hn⟩
  · simp only [hbn]
    by_cases hx : x ∈ Set.Icc (-((n:ℝ) + 1)) ((n:ℝ) + 1)
    · rw [Set.indicator_of_mem hx]; exact min_le_right _ _
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  · simp only [hbn]; exact Set.indicator_of_notMem hx _
  · refine le_trans (withDensity_mono (Eventually.of_forall fun x => ?_))
      (Measure.withDensity_rnDeriv_le G volume)
    simp only [hbn]
    by_cases hx : x ∈ Set.Icc (-((n:ℝ) + 1)) ((n:ℝ) + 1)
    · rw [Set.indicator_of_mem hx]; exact min_le_left _ _
    · rw [Set.indicator_of_notMem hx]; exact bot_le

lemma lattice_convPow (F : Measure ℝ) [IsProbabilityMeasure F] (L : Set ℝ) (hL : MeasurableSet L)
    (h0 : (0:ℝ) ∈ L) (hadd : ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L) (hF : F Lᶜ = 0) :
    ∀ n, convPow F n Lᶜ = 0
  | 0 => by
      rw [convPow, Measure.dirac_apply' _ hL.compl]
      simp [h0]
  | n + 1 => by
      have := convPow_isProb F n
      rw [convPow, Measure.conv, Measure.map_apply measurable_add hL.compl]
      refine measure_mono_null (t := (Lᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Lᶜ)) ?_
        (measure_union_null ?_ ?_)
      · intro p hp
        simp only [Set.mem_preimage, Set.mem_compl_iff] at hp
        simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true,
          true_and]
        by_contra hc
        push Not at hc
        exact hp (hadd _ hc.1 _ hc.2)
      · rw [Measure.prod_prod, lattice_convPow F L hL h0 hadd hF n, zero_mul]
      · rw [Measure.prod_prod, hF, mul_zero]

lemma aperiodic_of_classS (F : Measure ℝ) (hF : IsCycleLaw F) (hS : InClassS F) :
    IsAperiodic F := by
  have hP := hF.1
  rintro ⟨w, -, hL⟩
  obtain ⟨k, -, hk⟩ := hS
  set L : Set ℝ := {x : ℝ | ∃ n : ℕ, x = (n : ℝ) * w} with hLdef
  have hLc : L.Countable := by
    have : L = Set.range (fun n : ℕ => (n : ℝ) * w) := by
      ext x; simp [hLdef, eq_comm]
    rw [this]; exact Set.countable_range _
  have hLm : MeasurableSet L := hLc.measurableSet
  have hFc : F Lᶜ = 0 := by
    rw [measure_compl hLm (measure_ne_top _ _), hL, measure_univ]; simp
  apply hk
  refine ⟨Lᶜ, hLm.compl, lattice_convPow F L hLm ⟨0, by simp⟩ ?_ hFc k, ?_⟩
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩; exact ⟨a + b, by push_cast; ring⟩
  · rw [compl_compl]; exact hLc.measure_zero _

/-- `Tm X e u = ∫ e(u - y) dX(y)`. -/
noncomputable def Tm (X : Measure ℝ) (e : ℝ → ENNReal) (u : ℝ) : ENNReal := ∫⁻ y, e (u - y) ∂X

lemma measurable_Tm (X : Measure ℝ) [SFinite X] (e : ℝ → ENNReal) (he : Measurable e) :
    Measurable (Tm X e) :=
  (he.comp measurable_sub).lintegral_prod_right'

lemma measurable_iter_Tm (X : Measure ℝ) [SFinite X] (e : ℝ → ENNReal) (he : Measurable e) :
    ∀ n : ℕ, Measurable ((Tm X)^[n] e)
  | 0 => he
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact measurable_Tm X _ (measurable_iter_Tm X e he n)

lemma swap_T (X Y : Measure ℝ) [SFinite X] [SFinite Y] (e : ℝ → ENNReal) (he : Measurable e)
    (t : ℝ) : ∫⁻ y, (∫⁻ x, e (t - (y + x)) ∂Y) ∂X = Tm Y (Tm X e) t := by
  unfold Tm
  rw [lintegral_lintegral_swap]
  · congr 1; funext x; congr 1; funext y; congr 1; ring
  · exact (he.comp (measurable_const.sub (measurable_fst.add measurable_snd))).aemeasurable

lemma U_rec (F : Measure ℝ) [IsProbabilityMeasure F] (k : ℕ) (B R : Measure ℝ) [SFinite B]
    [SFinite R] (hGBR : convPow F k = R + B) (e : ℝ → ENNReal) (he : Measurable e) (t : ℝ) :
    Tm (U F) e t = (∑ j ∈ Finset.range k, Tm (convPow F j) e t) + Tm (U F) (Tm B e) t +
      Tm (U F) (Tm R e) t := by
  have := U_sfinite F
  have hg : Measurable (fun x => e (t - x)) := he.comp (measurable_const.sub measurable_id)
  have h1 := U_decomp F (fun x => e (t - x)) hg k
  rw [hGBR, lintegral_add_measure, swap_T R (U F) e he t, swap_T B (U F) e he t] at h1
  show ∫⁻ x, e (t - x) ∂(U F) = _
  rw [h1, add_assoc, add_comm (Tm (U F) (Tm R e) t)]
  rfl

lemma U_iter (F : Measure ℝ) [IsProbabilityMeasure F] (k : ℕ) (B R : Measure ℝ) [SFinite B]
    [SFinite R] (hGBR : convPow F k = R + B) (e : ℝ → ENNReal) (he : Measurable e) (t : ℝ) :
    ∀ N : ℕ, Tm (U F) e t = (∑ n ∈ Finset.range N,
      ((∑ j ∈ Finset.range k, Tm (convPow F j) ((Tm R)^[n] e) t) +
        Tm (U F) (Tm B ((Tm R)^[n] e)) t)) + Tm (U F) ((Tm R)^[N] e) t
  | 0 => by simp
  | N + 1 => by
      rw [U_iter F k B R hGBR e he t N, U_rec F k B R hGBR _ (measurable_iter_Tm R e he N) t,
        Finset.sum_range_succ, Function.iterate_succ_apply']
      ring

lemma TB_bound (F : Measure ℝ) [IsProbabilityMeasure F] (b : ℝ → ENNReal) (M : ℝ)
    (hb : Measurable b) (hbM : ∀ x, b x ≤ ENNReal.ofReal M)
    (hbs : ∀ x, x ∉ Set.Icc (-M) M → b x = 0)
    (Cw : ENNReal) (hCw : ∀ a, U F (Set.Icc (a - M) (a + M)) ≤ Cw)
    (h : ℝ → ENNReal) (hh : Measurable h) (t : ℝ) :
    Tm (U F) (Tm (volume.withDensity b) h) t ≤ ENNReal.ofReal M * Cw * ∫⁻ v, h v := by
  have := U_sfinite F
  set I : ℝ → ENNReal := (Set.Icc (-M) M).indicator 1 with hI
  have hIm : Measurable I := measurable_one.indicator measurableSet_Icc
  have hpt : ∀ u, Tm (volume.withDensity b) h u ≤ ENNReal.ofReal M * ∫⁻ v, I (u - v) * h v := by
    intro u
    unfold Tm
    have hmu : Measurable (fun y => h (u - y)) := hh.comp (measurable_const.sub measurable_id)
    rw [lintegral_withDensity_eq_lintegral_mul _ hb hmu]
    have e1 : ∫⁻ v, I (u - v) * h v = ∫⁻ y, I y * h (u - y) := by
      rw [← lintegral_sub_left_eq_self (fun v => I (u - v) * h v) u]
      congr 1; funext y; simp only [sub_sub_cancel]
    rw [e1]
    have hm3 : Measurable fun y => I y * h (u - y) := hIm.mul hmu
    refine le_trans (lintegral_mono fun y => ?_) (le_of_eq (lintegral_const_mul _ hm3))
    simp only [Pi.mul_apply]
    by_cases hy : y ∈ Set.Icc (-M) M
    · rw [hI, Set.indicator_of_mem hy, Pi.one_apply, one_mul]
      gcongr
      exact hbM y
    · rw [hbs y hy, zero_mul]; exact bot_le
  have hjm : Measurable (fun p : ℝ × ℝ => I (t - p.1 - p.2) * h p.2) :=
    (hIm.comp ((measurable_const.sub measurable_fst).sub measurable_snd)).mul
      (hh.comp measurable_snd)
  have hwin : ∀ v, ∫⁻ x, I (t - x - v) ∂(U F) = U F (Set.Icc ((t - v) - M) ((t - v) + M)) := by
    intro v
    rw [← lintegral_indicator_one measurableSet_Icc]
    congr 1; funext x
    simp only [hI, Set.indicator_apply, Set.mem_Icc, Pi.one_apply]
    by_cases h1 : -M ≤ t - x - v ∧ t - x - v ≤ M
    · have h2 : t - v - M ≤ x ∧ x ≤ t - v + M := ⟨by linarith [h1.2], by linarith [h1.1]⟩
      rw [if_pos h1, if_pos h2]
    · have h2 : ¬ (t - v - M ≤ x ∧ x ≤ t - v + M) := fun h2 =>
        h1 ⟨by linarith [h2.2], by linarith [h2.1]⟩
      rw [if_neg h1, if_neg h2]
  calc Tm (U F) (Tm (volume.withDensity b) h) t
      = ∫⁻ x, Tm (volume.withDensity b) h (t - x) ∂(U F) := rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal M * (∫⁻ v, I (t - x - v) * h v) ∂(U F) :=
        lintegral_mono fun x => hpt (t - x)
    _ = ENNReal.ofReal M * ∫⁻ v, h v * U F (Set.Icc ((t - v) - M) ((t - v) + M)) := by
        have hm2 : Measurable fun x => ∫⁻ v, I (t - x - v) * h v := hjm.lintegral_prod_right'
        rw [lintegral_const_mul _ hm2, lintegral_lintegral_swap (μ := U F)
          (ν := volume) (f := fun x v => I (t - x - v) * h v) hjm.aemeasurable]
        congr 1
        refine lintegral_congr fun v => ?_
        have hm4 : Measurable fun x => I (t - x - v) :=
          hIm.comp ((measurable_const.sub measurable_id).sub measurable_const)
        rw [lintegral_mul_const _ hm4, hwin v, mul_comm]
    _ ≤ ENNReal.ofReal M * ∫⁻ v, h v * Cw := by
        gcongr with v
        exact hCw _
    _ = ENNReal.ofReal M * Cw * ∫⁻ v, h v := by
        rw [lintegral_mul_const _ hh]; ring

lemma TR_L1 (R : Measure ℝ) [SFinite R] (h : ℝ → ENNReal) (hh : Measurable h) :
    ∫⁻ u, Tm R h u = R Set.univ * ∫⁻ v, h v := by
  unfold Tm
  rw [lintegral_lintegral_swap (μ := volume) (ν := R) (f := fun u y => h (u - y))
    ((hh.comp measurable_sub).aemeasurable)]
  simp only [lintegral_sub_right_eq_self h]
  rw [lintegral_const, mul_comm]

lemma TR_sup (R : Measure ℝ) (hR : R (Set.Iio 0) = 0) (h : ℝ → ENNReal) (c : ENNReal)
    (hc : ∀ u, h u ≤ c) (hneg : ∀ u < 0, h u = 0) :
    (∀ u, Tm R h u ≤ c * R Set.univ) ∧ (∀ u < 0, Tm R h u = 0) := by
  constructor
  · intro u
    calc Tm R h u ≤ ∫⁻ y, c ∂(R) := lintegral_mono fun y => hc _
      _ = c * R Set.univ := lintegral_const c
  · intro u hu
    unfold Tm
    have hae : ∀ᵐ y ∂(R), y ∉ Set.Iio 0 := measure_eq_zero_iff_ae_notMem.1 hR
    rw [lintegral_congr_ae (g := fun _ => (0 : ENNReal)) ?_, lintegral_zero]
    filter_upwards [hae] with y hy
    simp only [Set.mem_Iio, not_lt] at hy
    exact hneg _ (by linarith)

lemma iter_sup (R : Measure ℝ) (hR : R (Set.Iio 0) = 0) (e : ℝ → ENNReal) (s : ENNReal)
    (hs : ∀ u, e u ≤ s) (hneg : ∀ u < 0, e u = 0) :
    ∀ n : ℕ, (∀ u, (Tm R)^[n] e u ≤ s * R Set.univ ^ n) ∧ (∀ u < 0, (Tm R)^[n] e u = 0)
  | 0 => ⟨fun u => by simpa using hs u, hneg⟩
  | n + 1 => by
      obtain ⟨h1, h2⟩ := iter_sup R hR e s hs hneg n
      obtain ⟨h3, h4⟩ := TR_sup R hR _ _ h1 h2
      rw [Function.iterate_succ_apply']
      exact ⟨fun u => by rw [pow_succ, ← mul_assoc]; exact h3 u, h4⟩

lemma iter_L1 (R : Measure ℝ) [SFinite R] (e : ℝ → ENNReal) (he : Measurable e) :
    ∀ n : ℕ, ∫⁻ u, (Tm R)^[n] e u = R Set.univ ^ n * ∫⁻ v, e v
  | 0 => by simp
  | n + 1 => by
      rw [Function.iterate_succ_apply', TR_L1 R _ (measurable_iter_Tm R e he n), iter_L1 R e he n,
        pow_succ]
      ring

lemma TU_last (F : Measure ℝ) [IsProbabilityMeasure F] (h : ℝ → ENNReal) (c : ENNReal)
    (hc : ∀ u, h u ≤ c) (hneg : ∀ u < 0, h u = 0) (t : ℝ) :
    Tm (U F) h t ≤ c * U F (Set.Iic t) := by
  unfold Tm
  calc ∫⁻ x, h (t - x) ∂(U F) ≤ ∫⁻ x, (Set.Iic t).indicator (fun _ => c) x ∂(U F) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Set.Iic t
        · rw [Set.indicator_of_mem hx]; exact hc _
        · rw [Set.indicator_of_notMem hx, hneg _ (by simp at hx; linarith)]
    _ = c * U F (Set.Iic t) := lintegral_indicator_const measurableSet_Iic c

/-- The structural bound: `U ≤ (finite part) + D·Lebesgue`, in the convolution form. -/
lemma U_struct (F : Measure ℝ) [IsProbabilityMeasure F] (hneg : F (Set.Iio 0) = 0) (k : ℕ)
    (b : ℝ → ENNReal) (M : ℝ) (hb : Measurable b) (hbM : ∀ x, b x ≤ ENNReal.ofReal M)
    (hbs : ∀ x, x ∉ Set.Icc (-M) M → b x = 0) (hBG : volume.withDensity b ≤ convPow F k)
    (hbpos : 0 < ∫⁻ x, b x)
    (Cw : ENNReal) (hCw : ∀ a, U F (Set.Icc (a - M) (a + M)) ≤ Cw)
    (hUt : ∀ t, U F (Set.Iic t) ≠ ⊤)
    (e : ℝ → ENNReal) (he : Measurable e) (s : ENNReal) (hs_top : s ≠ ⊤) (hs : ∀ u, e u ≤ s)
    (heneg : ∀ u < 0, e u = 0) (t : ℝ) :
    Tm (U F) e t ≤ (∑' n, ∑ j ∈ Finset.range k,
        Tm (convPow F j) ((Tm (convPow F k - volume.withDensity b))^[n] e) t) +
      ENNReal.ofReal M * Cw * (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹ *
        ∫⁻ v, e v := by
  have hGP := convPow_isProb F k
  have : IsFiniteMeasure (volume.withDensity b) :=
    ⟨lt_of_le_of_lt (hBG Set.univ) (measure_lt_top _ _)⟩
  have : IsFiniteMeasure (convPow F k - volume.withDensity b) :=
    ⟨lt_of_le_of_lt (Measure.sub_le Set.univ) (measure_lt_top (convPow F k) _)⟩
  have hGBR : convPow F k = (convPow F k - volume.withDensity b) + volume.withDensity b :=
    (Measure.sub_add_cancel_of_le hBG).symm
  have hRneg : (convPow F k - volume.withDensity b) (Set.Iio 0) = 0 :=
    le_antisymm (le_trans (Measure.sub_le (Set.Iio 0)) (le_of_eq (convPow_Iio F hneg k))) bot_le
  have hrlt : (convPow F k - volume.withDensity b) Set.univ < 1 := by
    rw [Measure.sub_apply MeasurableSet.univ hBG, measure_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hbpos.ne'
  have hbound : ∀ N : ℕ, Tm (U F) e t ≤ (∑' n, ∑ j ∈ Finset.range k,
        Tm (convPow F j) ((Tm (convPow F k - volume.withDensity b))^[n] e) t) +
      ENNReal.ofReal M * Cw * (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹ *
        (∫⁻ v, e v) + s * (convPow F k - volume.withDensity b) Set.univ ^ N * U F (Set.Iic t) := by
    intro N
    rw [U_iter F k _ _ hGBR e he t N, Finset.sum_add_distrib]
    have hsup := iter_sup _ hRneg e s hs heneg N
    refine add_le_add (add_le_add (ENNReal.sum_le_tsum _) ?_) ?_
    · calc ∑ n ∈ Finset.range N, Tm (U F) (Tm (volume.withDensity b)
            ((Tm (convPow F k - volume.withDensity b))^[n] e)) t
          ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal M * Cw *
              ((convPow F k - volume.withDensity b) Set.univ ^ n * ∫⁻ v, e v) := by
            gcongr with n hn
            rw [← iter_L1 _ e he n]
            exact TB_bound F b M hb hbM hbs Cw hCw _ (measurable_iter_Tm _ e he n) t
        _ = ENNReal.ofReal M * Cw * (∑ n ∈ Finset.range N,
              (convPow F k - volume.withDensity b) Set.univ ^ n) * ∫⁻ v, e v := by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun n _ => by ring
        _ ≤ ENNReal.ofReal M * Cw * (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹ *
              ∫⁻ v, e v := by
            gcongr
            rw [← ENNReal.tsum_geometric]
            exact ENNReal.sum_le_tsum _
    · exact TU_last F _ _ hsup.1 hsup.2 t
  have h2 : Tendsto (fun N : ℕ => s * (convPow F k - volume.withDensity b) Set.univ ^ N *
      U F (Set.Iic t)) atTop (𝓝 0) := by
    have h1 := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrlt
    simpa using ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul h1 (Or.inr hs_top))
      (Or.inr (hUt t))
  have key : ∀ c : ENNReal, Tendsto (fun N : ℕ => c + s * (convPow F k - volume.withDensity b)
      Set.univ ^ N * U F (Set.Iic t)) atTop (𝓝 c) := fun c => by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).add h2
  exact ge_of_tendsto' (key _) hbound

/-! ## H: the error bound `limsup ∫ e(t - x) dH_K ≤ D ∫ e` for a spread-out cycle law -/

lemma Tm_le (X : Measure ℝ) (h : ℝ → ENNReal) (c : ENNReal) (hc : ∀ u, h u ≤ c) (u : ℝ) :
    Tm X h u ≤ c * X Set.univ :=
  le_trans (lintegral_mono fun y => hc (u - y)) (le_of_eq (lintegral_const c))

lemma Tm_tendsto_zero (X : Measure ℝ) [IsFiniteMeasure X] (h : ℝ → ENNReal) (hh : Measurable h)
    (c : ENNReal) (hc_top : c ≠ ⊤) (hc : ∀ u, h u ≤ c) (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (Tm X h) atTop (𝓝 0) := by
  have key := tendsto_lintegral_filter_of_dominated_convergence (μ := X) (l := atTop)
    (F := fun u y => h (u - y)) (f := fun _ => 0) (fun _ => c)
    (Eventually.of_forall fun u => hh.comp (measurable_const.sub measurable_id))
    (Eventually.of_forall fun u => ae_of_all _ fun y => hc _)
    (by rw [lintegral_const]; exact ENNReal.mul_ne_top hc_top (measure_ne_top X _))
    (ae_of_all _ fun y => hlim.comp ((tendsto_atTop_add_const_right atTop (-y) tendsto_id).congr
      fun u => by simp [sub_eq_add_neg]))
  show Tendsto (fun u => ∫⁻ y, h (u - y) ∂X) atTop (𝓝 0)
  simpa using key

lemma iter_tendsto_zero (R : Measure ℝ) [IsFiniteMeasure R] (hR : R (Set.Iio 0) = 0)
    (e : ℝ → ENNReal) (he : Measurable e) (s : ENNReal) (hs_top : s ≠ ⊤) (hs : ∀ u, e u ≤ s)
    (heneg : ∀ u < 0, e u = 0) (hlim : Tendsto e atTop (𝓝 0)) :
    ∀ n : ℕ, Tendsto ((Tm R)^[n] e) atTop (𝓝 0)
  | 0 => hlim
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact Tm_tendsto_zero R _ (measurable_iter_Tm R e he n) _
        (ENNReal.mul_ne_top hs_top (ENNReal.pow_ne_top (measure_ne_top R _)))
        (iter_sup R hR e s hs heneg n).1 (iter_tendsto_zero R hR e he s hs_top hs heneg hlim n)

lemma fin_term_le (F : Measure ℝ) [IsProbabilityMeasure F] (k : ℕ) (R : Measure ℝ)
    (hR : R (Set.Iio 0) = 0) (e : ℝ → ENNReal) (s : ENNReal) (hs : ∀ u, e u ≤ s)
    (heneg : ∀ u < 0, e u = 0) (n : ℕ) (t : ℝ) :
    ∑ j ∈ Finset.range k, Tm (convPow F j) ((Tm R)^[n] e) t ≤ k * (s * R Set.univ ^ n) := by
  calc _ ≤ ∑ j ∈ Finset.range k, s * R Set.univ ^ n * convPow F j Set.univ :=
        Finset.sum_le_sum fun j _ => Tm_le _ _ _ (iter_sup R hR e s hs heneg n).1 t
    _ = k * (s * R Set.univ ^ n) := by
        have : ∀ j, convPow F j Set.univ = 1 := fun j => by
          have := convPow_isProb F j; exact measure_univ
        simp [this]

lemma fin_tendsto (F : Measure ℝ) [IsProbabilityMeasure F] (k : ℕ) (R : Measure ℝ)
    [IsFiniteMeasure R] (hR : R (Set.Iio 0) = 0) (hr : R Set.univ < 1)
    (e : ℝ → ENNReal) (he : Measurable e) (s : ENNReal) (hs_top : s ≠ ⊤) (hs : ∀ u, e u ≤ s)
    (heneg : ∀ u < 0, e u = 0) (hlim : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun t => ∑' n, ∑ j ∈ Finset.range k, Tm (convPow F j) ((Tm R)^[n] e) t) atTop
      (𝓝 0) := by
  have hterm : ∀ n, Tendsto (fun t => ∑ j ∈ Finset.range k, Tm (convPow F j) ((Tm R)^[n] e) t)
      atTop (𝓝 0) := by
    intro n
    have := tendsto_finset_sum (Finset.range k) (fun j _ => by
      have := convPow_isProb F j
      exact Tm_tendsto_zero (convPow F j) _ (measurable_iter_Tm R e he n) _
        (ENNReal.mul_ne_top hs_top (ENNReal.pow_ne_top (measure_ne_top R _)))
        (iter_sup R hR e s hs heneg n).1 (iter_tendsto_zero R hR e he s hs_top hs heneg hlim n))
    simpa using this
  have key := tendsto_lintegral_filter_of_dominated_convergence (μ := Measure.count) (l := atTop)
    (F := fun t n => ∑ j ∈ Finset.range k, Tm (convPow F j) ((Tm R)^[n] e) t) (f := fun _ => 0)
    (fun n => (k : ENNReal) * (s * R Set.univ ^ n))
    (Eventually.of_forall fun t => measurable_from_nat)
    (Eventually.of_forall fun t => ae_of_all _ fun n => fin_term_le F k R hR e s hs heneg n t)
    ?_ (ae_of_all _ fun n => hterm n)
  · simpa [lintegral_count] using key
  · rw [lintegral_count, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (ENNReal.mul_ne_top hs_top
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'))

lemma R_lt_one (F : Measure ℝ) [IsProbabilityMeasure F] (k : ℕ) (b : ℝ → ENNReal)
    (hBG : volume.withDensity b ≤ convPow F k) (hbpos : 0 < ∫⁻ x, b x) :
    (convPow F k - volume.withDensity b) Set.univ < 1 := by
  have hGP := convPow_isProb F k
  have : IsFiniteMeasure (volume.withDensity b) :=
    ⟨lt_of_le_of_lt (hBG Set.univ) (measure_lt_top _ _)⟩
  rw [Measure.sub_apply MeasurableSet.univ hBG, measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hbpos.ne'

theorem err_bound (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K) (hS : InClassS F) :
    ∃ D : ENNReal, D ≠ ⊤ ∧ ∀ e : ℝ → ENNReal, Measurable e → ∀ s : ENNReal, s ≠ ⊤ →
      (∀ u, e u ≤ s) → (∀ u < 0, e u = 0) → Tendsto e atTop (𝓝 0) →
      ∀ δ : ENNReal, 0 < δ → ∀ᶠ t in atTop,
        ∫⁻ x, e (t - x) ∂(renewalMeasure K F) ≤ D * (∫⁻ v, e v) + δ := by
  have hP := hF.1
  have hKf : IsFiniteMeasure K := ⟨lt_of_le_of_lt hK.2 ENNReal.one_lt_top⟩
  have hUs := U_sfinite F
  obtain ⟨k, -, hk⟩ := hS
  have hGP := convPow_isProb F k
  obtain ⟨b, M, hb, hM, hbM, hbs, hBG, hbpos⟩ := ac_piece (convPow F k) hk
  obtain ⟨C, hC0, hC⟩ := W_bdd F hF (2 * M + 1) (by linarith)
  have hCw : ∀ a, U F (Set.Icc (a - M) (a + M)) ≤ ENNReal.ofReal C := by
    intro a
    refine le_trans (measure_mono ?_)
      ((ENNReal.le_ofReal_iff_toReal_le (hC (a - M - 1)).1 hC0).2 (hC (a - M - 1)).2)
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioc]
    constructor <;> linarith [hx.1, hx.2]
  have hUt : ∀ t, U F (Set.Iic t) ≠ ⊤ := fun t => (U_Iic_lt_top F hF t).ne
  have hr := R_lt_one F k b hBG hbpos
  have : IsFiniteMeasure (volume.withDensity b) :=
    ⟨lt_of_le_of_lt (hBG Set.univ) (measure_lt_top _ _)⟩
  have hRf : IsFiniteMeasure (convPow F k - volume.withDensity b) :=
    ⟨lt_of_le_of_lt (Measure.sub_le Set.univ) (measure_lt_top (convPow F k) _)⟩
  have hRneg : (convPow F k - volume.withDensity b) (Set.Iio 0) = 0 :=
    le_antisymm (le_trans (Measure.sub_le (Set.Iio 0)) (le_of_eq (convPow_Iio F hF.2.1 k))) bot_le
  have hinv : (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'
  have hD0 : ENNReal.ofReal M * ENNReal.ofReal C *
      (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hinv
  refine ⟨K Set.univ * (ENNReal.ofReal M * ENNReal.ofReal C *
      (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹),
    ENNReal.mul_ne_top (measure_ne_top K _) hD0, ?_⟩
  intro e he s hs_top hs heneg hlim δ hδ
  set Fin : ℝ → ENNReal := fun t => ∑' n, ∑ j ∈ Finset.range k,
    Tm (convPow F j) ((Tm (convPow F k - volume.withDensity b))^[n] e) t with hFin
  have hFin_m : Measurable Fin := by
    refine Measurable.ennreal_tsum fun n => Finset.measurable_sum _ fun j _ => ?_
    have := convPow_isProb F j
    exact measurable_Tm _ _ (measurable_iter_Tm _ e he n)
  have hFin_lim := fin_tendsto F k _ hRneg hr e he s hs_top hs heneg hlim
  have hFin_bd : ∀ t, Fin t ≤ k * (s * (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹) := by
    intro t
    calc Fin t ≤ ∑' n : ℕ, (k : ENNReal) *
          (s * (convPow F k - volume.withDensity b) Set.univ ^ n) :=
          ENNReal.tsum_le_tsum fun n => fin_term_le F k _ hRneg e s hs heneg n t
      _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hbtop : (k : ENNReal) * (s * (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (ENNReal.mul_ne_top hs_top hinv)
  have hKlim : Tendsto (fun t => ∫⁻ x, Fin (t - x) ∂K) atTop (𝓝 0) := by
    have key := tendsto_lintegral_filter_of_dominated_convergence (μ := K) (l := atTop)
      (F := fun t x => Fin (t - x)) (f := fun _ => 0)
      (fun _ => (k : ENNReal) * (s * (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹))
      (Eventually.of_forall fun t => hFin_m.comp (measurable_const.sub measurable_id))
      (Eventually.of_forall fun t => ae_of_all _ fun x => hFin_bd _)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top hbtop (measure_ne_top K _))
      (ae_of_all _ fun x => hFin_lim.comp ((tendsto_atTop_add_const_right atTop (-x)
        tendsto_id).congr fun u => by simp [sub_eq_add_neg]))
    simpa using key
  filter_upwards [hKlim.eventually (gt_mem_nhds hδ)] with t ht
  have hm : Measurable (fun z => e (t - z)) := he.comp (measurable_const.sub measurable_id)
  calc ∫⁻ x, e (t - x) ∂(renewalMeasure K F)
      = ∫⁻ x, Tm (U F) e (t - x) ∂K := by
        rw [renewal_eq_conv F K, Measure.lintegral_conv hm]
        simp only [Tm, sub_add_eq_sub_sub]
    _ ≤ ∫⁻ x, (Fin (t - x) + ENNReal.ofReal M * ENNReal.ofReal C *
          (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹ * ∫⁻ v, e v) ∂K :=
        lintegral_mono fun x => U_struct F hF.2.1 k b M hb hbM hbs hBG hbpos _ hCw hUt e he s
          hs_top hs heneg (t - x)
    _ = ∫⁻ x, Fin (t - x) ∂K + K Set.univ * (ENNReal.ofReal M * ENNReal.ofReal C *
          (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹) * ∫⁻ v, e v := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]; ring
    _ ≤ K Set.univ * (ENNReal.ofReal M * ENNReal.ofReal C *
          (1 - (convPow F k - volume.withDensity b) Set.univ)⁻¹) * (∫⁻ v, e v) + δ := by
        rw [add_comm]; exact add_le_add le_rfl ht.le

/-! ## I: step functions, their key renewal theorem, and L¹ density -/

noncomputable def stepF (N : ℕ) (a p q : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, a j * ((Set.Icc 0 (q j)).indicator (fun _ => (1:ℝ)) u -
    (Set.Icc 0 (p j)).indicator (fun _ => (1:ℝ)) u)

lemma measurable_stepF (N : ℕ) (a p q : ℕ → ℝ) : Measurable (stepF N a p q) := by
  unfold stepF
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul
    ((measurable_const.indicator measurableSet_Icc).sub
      (measurable_const.indicator measurableSet_Icc))

lemma ind_diff_abs (p q u : ℝ) :
    |(Set.Icc 0 q).indicator (fun _ => (1:ℝ)) u - (Set.Icc 0 p).indicator (fun _ => (1:ℝ)) u|
      ≤ 1 := by
  by_cases h1 : u ∈ Set.Icc 0 q <;> by_cases h2 : u ∈ Set.Icc 0 p <;> simp [h1, h2]

lemma stepF_abs_le (N : ℕ) (a p q : ℕ → ℝ) (u : ℝ) :
    |stepF N a p q u| ≤ ∑ j ∈ Finset.range N, |a j| := by
  unfold stepF
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ind_diff_abs _ _ _)

lemma stepF_zero_of_gt (N : ℕ) (a p q : ℕ → ℝ) (u : ℝ)
    (hu : ∑ j ∈ Finset.range N, (|p j| + |q j|) < u) : stepF N a p q u = 0 := by
  unfold stepF
  refine Finset.sum_eq_zero fun j hj => ?_
  have h1 : |p j| + |q j| ≤ ∑ j ∈ Finset.range N, (|p j| + |q j|) :=
    Finset.single_le_sum (f := fun j => |p j| + |q j|) (fun i _ => by positivity) hj
  have hp : p j < u := by linarith [le_abs_self (p j), abs_nonneg (q j)]
  have hq : q j < u := by linarith [le_abs_self (q j), abs_nonneg (p j)]
  rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 hq)),
    Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 hp))]
  ring

lemma ind_integrable (q : ℝ) : Integrable ((Set.Icc 0 q).indicator (fun _ => (1:ℝ))) :=
  (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc

lemma stepF_integrable (N : ℕ) (a p q : ℕ → ℝ) : Integrable (stepF N a p q) := by
  unfold stepF
  exact integrable_finset_sum _ fun j _ =>
    ((ind_integrable _).sub (ind_integrable _)).const_mul _

lemma ind_integral_Ioi (q : ℝ) (hq : 0 ≤ q) :
    ∫ v in Set.Ioi 0, (Set.Icc 0 q).indicator (fun _ => (1:ℝ)) v = q := by
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have : Set.Icc 0 q ∩ Set.Ioi 0 = Set.Ioc 0 q := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioc]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
  rw [this, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hq]

lemma stepF_integral_Ioi (N : ℕ) (a p q : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) :
    ∫ v in Set.Ioi 0, stepF N a p q v = ∑ j ∈ Finset.range N, a j * (q j - p j) := by
  unfold stepF
  have hi : ∀ j ∈ Finset.range N, Integrable (fun v => a j * ((Set.Icc 0 (q j)).indicator
      (fun _ => (1:ℝ)) v - (Set.Icc 0 (p j)).indicator (fun _ => (1:ℝ)) v))
      (volume.restrict (Set.Ioi 0)) := fun j _ =>
    (((ind_integrable _).sub (ind_integrable _)).const_mul _).integrableOn
  rw [integral_finset_sum _ hi]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_sub (ind_integrable _).integrableOn (ind_integrable _).integrableOn,
    ind_integral_Ioi _ (hq j), ind_integral_Ioi _ (hp j)]

lemma intOn_bdd (H : Measure ℝ) (t : ℝ) (hHt : H (Set.Icc 0 t) ≠ ⊤) (f : ℝ → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ u, 0 ≤ u → |f u| ≤ C) :
    Integrable (fun s => f (t - s)) (H.restrict (Set.Icc 0 t)) := by
  have : IsFiniteMeasure (H.restrict (Set.Icc 0 t)) := isFiniteMeasure_restrict.2 hHt
  refine Integrable.mono' (integrable_const C)
    (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs]
  exact hC _ (by linarith [hs.2])

lemma krt_Icc (H : Measure ℝ) (c : ℝ) (hc : 0 ≤ c) (hneg : H (Set.Iio 0) = 0)
    (hfin : ∀ a b : ℝ, H (Set.Ioc a b) ≠ ⊤)
    (hbdd : ∀ h > 0, ∃ C : ℝ, ∀ t, (H (Set.Ioc t (t + h))).toReal ≤ C)
    (hbw : ∀ h > 0, Tendsto (fun t => (H (Set.Ioc t (t + h))).toReal) atTop (𝓝 (c * h)))
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun t => ∫ s in Set.Icc 0 t, (Set.Icc 0 q).indicator (fun _ => (1:ℝ)) (t - s) ∂H)
      atTop (𝓝 (c * q)) := by
  have h := krt_abstract H c hc hneg hfin hbdd hbw ((Set.Icc 0 q).indicator (fun _ => (1:ℝ)))
    (measurable_const.indicator measurableSet_Icc)
    ⟨1, fun v _ => by by_cases hv : v ∈ Set.Icc 0 q <;> simp [hv]⟩ ?_
    (ind_integrable q).integrableOn
  · rwa [ind_integral_Ioi q hq] at h
  · intro x hx y hy hxy
    by_cases hy' : y ∈ Set.Icc 0 q
    · have hx' : x ∈ Set.Icc 0 q := ⟨le_of_lt hx, le_trans hxy hy'.2⟩
      simp [hy', hx']
    · rw [Set.indicator_of_notMem hy']
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma krt_step (H : Measure ℝ) (c : ℝ) (hc : 0 ≤ c) (hneg : H (Set.Iio 0) = 0)
    (hfin : ∀ a b : ℝ, H (Set.Ioc a b) ≠ ⊤)
    (hbdd : ∀ h > 0, ∃ C : ℝ, ∀ t, (H (Set.Ioc t (t + h))).toReal ≤ C)
    (hbw : ∀ h > 0, Tendsto (fun t => (H (Set.Ioc t (t + h))).toReal) atTop (𝓝 (c * h)))
    (hHt : ∀ t, H (Set.Icc 0 t) ≠ ⊤) (N : ℕ) (a p q : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hq : ∀ j, 0 ≤ q j) :
    Tendsto (fun t => ∫ s in Set.Icc 0 t, stepF N a p q (t - s) ∂H) atTop
      (𝓝 (c * ∫ v in Set.Ioi 0, stepF N a p q v)) := by
  rw [stepF_integral_Ioi N a p q hp hq, Finset.mul_sum]
  have hint : ∀ r t : ℝ, Integrable (fun s => (Set.Icc 0 r).indicator (fun _ => (1:ℝ)) (t - s))
      (H.restrict (Set.Icc 0 t)) := fun r t =>
    intOn_bdd H t (hHt t) _ (measurable_const.indicator measurableSet_Icc) 1
      (fun u _ => by by_cases h : u ∈ Set.Icc 0 r <;> simp [h])
  have heq : (fun t => ∫ s in Set.Icc 0 t, stepF N a p q (t - s) ∂H) = fun t =>
      ∑ j ∈ Finset.range N, a j *
        (∫ s in Set.Icc 0 t, (Set.Icc 0 (q j)).indicator (fun _ => (1:ℝ)) (t - s) ∂H -
          ∫ s in Set.Icc 0 t, (Set.Icc 0 (p j)).indicator (fun _ => (1:ℝ)) (t - s) ∂H) := by
    funext t
    unfold stepF
    have hi : ∀ j ∈ Finset.range N, Integrable (fun s => a j * ((Set.Icc 0 (q j)).indicator
        (fun _ => (1:ℝ)) (t - s) - (Set.Icc 0 (p j)).indicator (fun _ => (1:ℝ)) (t - s)))
        (H.restrict (Set.Icc 0 t)) := fun j _ => ((hint _ t).sub (hint _ t)).const_mul _
    rw [integral_finset_sum _ hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_sub (hint _ t) (hint _ t)]
  rw [heq]
  refine tendsto_finset_sum _ fun j _ => ?_
  have h1 := krt_Icc H c hc hneg hfin hbdd hbw (q j) (hq j)
  have h2 := krt_Icc H c hc hneg hfin hbdd hbw (p j) (hp j)
  convert (h1.sub h2).const_mul (a j) using 2
  ring

lemma grid_term (j : ℕ) (h u : ℝ) (hh : 0 < h) (hu : 0 < u) :
    (Set.Icc 0 (((j:ℝ) + 1) * h)).indicator (fun _ => (1:ℝ)) u -
      (Set.Icc 0 ((j:ℝ) * h)).indicator (fun _ => (1:ℝ)) u =
      if (j:ℝ) * h < u ∧ u ≤ ((j:ℝ) + 1) * h then 1 else 0 := by
  simp only [Set.indicator_apply, Set.mem_Icc, hu.le, true_and]
  by_cases h1 : u ≤ ((j:ℝ) + 1) * h <;> by_cases h2 : u ≤ (j:ℝ) * h
  · rw [if_pos h1, if_pos h2, if_neg (fun h' => absurd h2 (not_le.2 h'.1))]; norm_num
  · rw [if_pos h1, if_neg h2, if_pos ⟨not_le.1 h2, h1⟩]; norm_num
  · exfalso; apply h1; nlinarith
  · rw [if_neg h1, if_neg h2, if_neg (fun h' => h1 h'.2)]; norm_num

lemma ceil_facts (h u : ℝ) (hh : 0 < h) (hu : 0 < u) :
    1 ≤ ⌈u / h⌉₊ ∧ u ≤ (⌈u / h⌉₊ : ℝ) * h ∧ ((⌈u / h⌉₊ : ℝ) - 1) * h < u := by
  refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (div_pos hu hh)).ne', ?_, ?_⟩
  · have := Nat.le_ceil (u / h); rwa [div_le_iff₀ hh] at this
  · have := Nat.ceil_lt_add_one (div_nonneg hu.le hh.le)
    have h2 : (⌈u / h⌉₊ : ℝ) - 1 < u / h := by linarith
    rwa [lt_div_iff₀ hh] at h2

lemma stepF_grid_in (N : ℕ) (h : ℝ) (hh : 0 < h) (g : ℝ → ℝ) (u : ℝ) (hu : 0 < u)
    (huN : u ≤ N * h) :
    stepF N (fun j => g (((j:ℝ) + 1) * h)) (fun j => (j:ℝ) * h) (fun j => ((j:ℝ) + 1) * h) u =
      g ((⌈u / h⌉₊ : ℝ) * h) := by
  obtain ⟨hn1, hle, hlt⟩ := ceil_facts h u hh hu
  have hnN : ⌈u / h⌉₊ ≤ N := Nat.ceil_le.2 (by rw [div_le_iff₀ hh]; exact huN)
  have hcast : ((⌈u / h⌉₊ - 1 : ℕ) : ℝ) = (⌈u / h⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  show ∑ j ∈ Finset.range N, g (((j:ℝ) + 1) * h) *
      ((Set.Icc 0 (((j:ℝ) + 1) * h)).indicator (fun _ => (1:ℝ)) u -
        (Set.Icc 0 ((j:ℝ) * h)).indicator (fun _ => (1:ℝ)) u) = _
  rw [Finset.sum_eq_single_of_mem (⌈u / h⌉₊ - 1) (Finset.mem_range.2 (by omega))]
  · rw [grid_term _ h u hh hu, if_pos, mul_one, hcast, sub_add_cancel]
    rw [hcast, sub_add_cancel]
    exact ⟨hlt, hle⟩
  · intro j _ hj
    rw [grid_term _ h u hh hu, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    apply hj
    have a1 : (j:ℝ) < ⌈u / h⌉₊ := by
      by_contra hc; push Not at hc
      have := mul_le_mul_of_nonneg_right hc hh.le
      linarith
    have a2 : (⌈u / h⌉₊ : ℝ) < j + 2 := by
      by_contra hc; push Not at hc
      have := mul_le_mul_of_nonneg_right hc hh.le
      have e1 : ((j:ℝ) + 2) * h = ((j:ℝ) + 1) * h + h := by ring
      have e2 : ((⌈u / h⌉₊ : ℝ) - 1) * h = (⌈u / h⌉₊ : ℝ) * h - h := by ring
      linarith
    have b1 : j < ⌈u / h⌉₊ := by exact_mod_cast a1
    have b2 : ⌈u / h⌉₊ < j + 2 := by exact_mod_cast a2
    omega

lemma stepF_grid_out (N : ℕ) (h : ℝ) (hh : 0 < h) (g : ℝ → ℝ) (u : ℝ) (hu : (N:ℝ) * h < u) :
    stepF N (fun j => g (((j:ℝ) + 1) * h)) (fun j => (j:ℝ) * h) (fun j => ((j:ℝ) + 1) * h) u =
      0 := by
  have hu0 : 0 < u := lt_of_le_of_lt (by positivity) hu
  show ∑ j ∈ Finset.range N, g (((j:ℝ) + 1) * h) *
      ((Set.Icc 0 (((j:ℝ) + 1) * h)).indicator (fun _ => (1:ℝ)) u -
        (Set.Icc 0 ((j:ℝ) * h)).indicator (fun _ => (1:ℝ)) u) = 0
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjN : (j:ℝ) + 1 ≤ N := by
    have := Finset.mem_range.1 hj; exact_mod_cast this
  rw [grid_term _ h u hh hu0, if_neg, mul_zero]
  rintro ⟨-, h2⟩
  have := mul_le_mul_of_nonneg_right hjN hh.le
  linarith

lemma step_approx (Ψ : ℝ → ℝ) (hint : IntegrableOn Ψ (Set.Ioi 0)) (η : ℝ) (hη : 0 < η) :
    ∃ (N : ℕ) (a p q : ℕ → ℝ), (∀ j, 0 ≤ p j) ∧ (∀ j, 0 ≤ q j) ∧
      ∫ v in Set.Ioi 0, |Ψ v - stepF N a p q v| ≤ η := by
  have hf : Integrable ((Set.Ioi (0:ℝ)).indicator Ψ) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hint
  obtain ⟨g, hgc, hgle, hgcont, hgi⟩ := hf.exists_hasCompactSupport_integral_sub_le (half_pos hη)
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hR0 : ∀ x, R < |x| → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport (fun hmem => by
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith)
  set R0 := max R 0 with hR0def
  have hR0nn : 0 ≤ R0 := le_max_right _ _
  set ω := η / (2 * (R0 + 2)) with hω
  have hωpos : 0 < ω := by positivity
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1
    (hgc.uniformContinuous_of_continuous hgcont) ω hωpos
  set h := min (δ / 2) 1 with hhdef
  have hh : 0 < h := lt_min (half_pos hδ) one_pos
  have hhδ : h < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hh1 : h ≤ 1 := min_le_right _ _
  set N := ⌈R0 / h⌉₊ with hN
  have hNlo : R0 ≤ N * h := by
    have := Nat.le_ceil (R0 / h); rwa [div_le_iff₀ hh] at this
  have hNhi : (N:ℝ) * h ≤ R0 + 2 := by
    have := Nat.ceil_lt_add_one (div_nonneg hR0nn hh.le)
    have h2 : (N:ℝ) < R0 / h + 1 := this
    have h3 : (N:ℝ) * h < (R0 / h + 1) * h := mul_lt_mul_of_pos_right h2 hh
    rw [add_mul, div_mul_cancel₀ _ hh.ne'] at h3
    linarith
  set a : ℕ → ℝ := fun j => g (((j:ℝ) + 1) * h) with ha
  set p : ℕ → ℝ := fun j => (j:ℝ) * h with hp
  set q : ℕ → ℝ := fun j => ((j:ℝ) + 1) * h with hq
  refine ⟨N, a, p, q, fun j => by positivity, fun j => by positivity, ?_⟩
  have hσi := (stepF_integrable N a p q).integrableOn (s := Set.Ioi (0:ℝ))
  have hgσ : ∀ u ∈ Set.Ioi (0:ℝ), |g u - stepF N a p q u| ≤
      (Set.Ioc 0 ((N:ℝ) * h)).indicator (fun _ => ω) u := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    by_cases huN : u ≤ N * h
    · rw [Set.indicator_of_mem (show u ∈ Set.Ioc 0 ((N:ℝ) * h) from ⟨hu0, huN⟩),
        stepF_grid_in N h hh g u hu0 huN]
      obtain ⟨-, hle, hlt⟩ := ceil_facts h u hh hu0
      have hd : dist u ((⌈u / h⌉₊ : ℝ) * h) < δ := by
        have e2 : ((⌈u / h⌉₊ : ℝ) - 1) * h = (⌈u / h⌉₊ : ℝ) * h - h := by ring
        rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith
      have := hδg hd
      rw [Real.dist_eq] at this
      exact this.le
    · push Not at huN
      rw [Set.indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 huN)),
        stepF_grid_out N h hh g u huN, hR0 u (by rw [abs_of_pos hu0]; linarith [le_max_left R 0])]
      simp
  have h1 : ∫ v in Set.Ioi 0, |Ψ v - g v| ≤ η / 2 := by
    calc ∫ v in Set.Ioi 0, |Ψ v - g v| = ∫ v in Set.Ioi 0, ‖(Set.Ioi (0:ℝ)).indicator Ψ v - g v‖ := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
          simp [Set.indicator_of_mem hv, Real.norm_eq_abs]
      _ ≤ ∫ v, ‖(Set.Ioi (0:ℝ)).indicator Ψ v - g v‖ :=
          setIntegral_le_integral (hf.sub hgi).norm (ae_of_all _ fun v => norm_nonneg _)
      _ ≤ η / 2 := hgle
  have h2 : ∫ v in Set.Ioi 0, |g v - stepF N a p q v| ≤ η / 2 := by
    calc ∫ v in Set.Ioi 0, |g v - stepF N a p q v|
        ≤ ∫ v in Set.Ioi 0, (Set.Ioc 0 ((N:ℝ) * h)).indicator (fun _ => ω) v :=
          setIntegral_mono_on (hgi.integrableOn.sub hσi).abs
            ((integrable_indicator_iff measurableSet_Ioc).2
              continuous_const.integrableOn_Ioc).integrableOn measurableSet_Ioi hgσ
      _ = ω * (N * h) := by
          rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
            Set.Ioc_inter_Ioi, max_self, setIntegral_const, measureReal_def, Real.volume_Ioc,
            sub_zero, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_comm]
      _ ≤ ω * (R0 + 2) := by gcongr
      _ = η / 2 := by rw [hω]; field_simp
  have i1 : IntegrableOn (fun v => |Ψ v - g v|) (Set.Ioi 0) := (hint.sub hgi.integrableOn).abs
  have i2 : IntegrableOn (fun v => |g v - stepF N a p q v|) (Set.Ioi 0) :=
    (hgi.integrableOn.sub hσi).abs
  have i0 : IntegrableOn (fun v => |Ψ v - stepF N a p q v|) (Set.Ioi 0) := (hint.sub hσi).abs
  calc ∫ v in Set.Ioi 0, |Ψ v - stepF N a p q v|
      ≤ ∫ v in Set.Ioi 0, (|Ψ v - g v| + |g v - stepF N a p q v|) :=
        setIntegral_mono_on i0 (i1.add i2) measurableSet_Ioi (fun v _ => abs_sub_le _ _ _)
    _ = (∫ v in Set.Ioi 0, |Ψ v - g v|) + ∫ v in Set.Ioi 0, |g v - stepF N a p q v| :=
        integral_add i1 i2
    _ ≤ η := by linarith

lemma tendsto_of_approx (I : ℝ → ℝ) (L : ℝ)
    (h : ∀ ε > 0, ∃ J : ℝ → ℝ, ∃ l : ℝ, Tendsto J atTop (𝓝 l) ∧ |l - L| ≤ ε ∧
      ∀ᶠ t in atTop, |I t - J t| ≤ ε) : Tendsto I atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨J, l, hJ, hl, hIJ⟩ := h (ε / 4) (by positivity)
  filter_upwards [hIJ, Metric.tendsto_nhds.1 hJ (ε / 4) (by positivity)] with t h1 h2
  rw [Real.dist_eq] at h2 ⊢
  calc |I t - L| = |(I t - J t) + (J t - l) + (l - L)| := by congr 1; ring
    _ ≤ |I t - J t| + |J t - l| + |l - L| := abs_add_three _ _ _
    _ < ε := by linarith

/-! ## K: the key renewal theorem for a spread-out cycle law (Smith 1955, Theorem 1) -/

theorem krt_spread (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ) (hbdd : ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → |Ψ v| ≤ C)
    (hint : IntegrableOn Ψ (Set.Ioi 0)) (hlim : Tendsto Ψ atTop (𝓝 0)) (hS : InClassS F) :
    Tendsto (fun t : ℝ => ∫ s in Set.Icc 0 t, Ψ (t - s) ∂(renewalMeasure K F)) atTop
      (𝓝 ((K Set.univ).toReal * (mean F)⁻¹.toReal * ∫ v in Set.Ioi 0, Ψ v)) := by
  have hP := hF.1
  have hKf : IsFiniteMeasure K := ⟨lt_of_le_of_lt hK.2 ENNReal.one_lt_top⟩
  have hper := aperiodic_of_classS F hF hS
  have hneg := H_neg F K hF hK
  have hfin := H_fin F K hF hK
  have hbddH := H_bdd F K hF hK
  have hbw := H_blackwell F K hF hK hper
  obtain ⟨D, hDtop, hD⟩ := err_bound F K hF hK hS
  set H := renewalMeasure K F with hH
  set c := (K Set.univ).toReal * (mean F)⁻¹.toReal with hc
  have hc0 : 0 ≤ c := by positivity
  have hHt : ∀ t, H (Set.Icc 0 t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top (hfin (-1) t) (measure_mono fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  obtain ⟨C, hC⟩ := hbdd
  have hD0 : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  refine tendsto_of_approx _ _ fun ε hε => ?_
  set η := ε / (2 * (D.toReal + c + 1)) with hη
  have hden : 0 < 2 * (D.toReal + c + 1) := by positivity
  have hηpos : 0 < η := div_pos hε hden
  have hηε : (D.toReal + c + 1) * η = ε / 2 := by rw [hη]; field_simp
  obtain ⟨N, a, p, q, hp, hq, hap⟩ := step_approx Ψ hint η hηpos
  have hσint : IntegrableOn (stepF N a p q) (Set.Ioi 0) := (stepF_integrable N a p q).integrableOn
  refine ⟨fun t => ∫ s in Set.Icc 0 t, stepF N a p q (t - s) ∂H,
    c * ∫ v in Set.Ioi 0, stepF N a p q v,
    krt_step H c hc0 hneg hfin hbddH hbw hHt N a p q hp hq, ?_, ?_⟩
  · have h1 : |(∫ v in Set.Ioi 0, stepF N a p q v) - ∫ v in Set.Ioi 0, Ψ v| ≤ η := by
      rw [← integral_sub hσint hint]
      refine le_trans abs_integral_le_integral_abs ?_
      calc ∫ v in Set.Ioi 0, |stepF N a p q v - Ψ v|
          = ∫ v in Set.Ioi 0, |Ψ v - stepF N a p q v| := by
            congr 1; funext v; exact abs_sub_comm _ _
        _ ≤ η := hap
    rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    calc c * |(∫ v in Set.Ioi 0, stepF N a p q v) - ∫ v in Set.Ioi 0, Ψ v| ≤ c * η := by gcongr
      _ ≤ (D.toReal + c + 1) * η := by gcongr; linarith
      _ ≤ ε := by rw [hηε]; linarith
  · set e : ℝ → ENNReal := (Set.Ici 0).indicator
      (fun u => ENNReal.ofReal |Ψ u - stepF N a p q u|) with he
    have hem : Measurable e :=
      (ENNReal.measurable_ofReal.comp ((hΨm.sub (measurable_stepF N a p q)).abs)).indicator
        measurableSet_Ici
    have hes : ∀ u, e u ≤ ENNReal.ofReal (C + ∑ j ∈ Finset.range N, |a j|) := by
      intro u
      by_cases hu : u ∈ Set.Ici 0
      · rw [he, Set.indicator_of_mem hu]
        exact ENNReal.ofReal_le_ofReal (le_trans (abs_sub _ _)
          (add_le_add (hC u hu) (stepF_abs_le N a p q u)))
      · rw [he, Set.indicator_of_notMem hu]; exact bot_le
    have heneg : ∀ u < 0, e u = 0 := fun u hu => by
      rw [he, Set.indicator_of_notMem (by simpa using hu)]
    have helim : Tendsto e atTop (𝓝 0) := by
      have h1 : Tendsto (fun u => ENNReal.ofReal |Ψ u|) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hlim.abs
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (max (∑ j ∈ Finset.range N, (|p j| + |q j|)) 0)]
        with u hu
      have hu0 : u ∈ Set.Ici 0 := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hu)
      rw [he, Set.indicator_of_mem hu0,
        stepF_zero_of_gt N a p q u (lt_of_le_of_lt (le_max_left _ _) hu), sub_zero]
    have hi0 : IntegrableOn (fun v => |Ψ v - stepF N a p q v|) (Set.Ioi 0) := (hint.sub hσint).abs
    have hint_e : ∫⁻ v, e v = ENNReal.ofReal (∫ v in Set.Ioi 0, |Ψ v - stepF N a p q v|) := by
      rw [he, lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm,
        ofReal_integral_eq_lintegral_ofReal hi0 (ae_of_all _ fun v => abs_nonneg _)]
    have hel : ∫⁻ v, e v ≤ ENNReal.ofReal η := by
      rw [hint_e]; exact ENNReal.ofReal_le_ofReal hap
    have hel_top : ∫⁻ v, e v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hel
    filter_upwards [hD e hem _ ENNReal.ofReal_ne_top hes heneg helim (ENNReal.ofReal (ε / 2))
      (ENNReal.ofReal_pos.2 (half_pos hε))] with t ht
    have hIΨ : Integrable (fun s => Ψ (t - s)) (H.restrict (Set.Icc 0 t)) :=
      intOn_bdd H t (hHt t) Ψ hΨm C hC
    have hIσ : Integrable (fun s => stepF N a p q (t - s)) (H.restrict (Set.Icc 0 t)) :=
      intOn_bdd H t (hHt t) _ (measurable_stepF N a p q) _ (fun u _ => stepF_abs_le N a p q u)
    have hrhs_top : D * (∫⁻ v, e v) + ENNReal.ofReal (ε / 2) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hDtop hel_top, ENNReal.ofReal_ne_top⟩
    rw [← integral_sub hIΨ hIσ]
    refine le_trans abs_integral_le_integral_abs ?_
    calc ∫ s in Set.Icc 0 t, |Ψ (t - s) - stepF N a p q (t - s)| ∂H
        = (∫⁻ s in Set.Icc 0 t, e (t - s) ∂H).toReal := by
          have hm5 : AEStronglyMeasurable (fun s => |Ψ (t - s) - stepF N a p q (t - s)|)
              (H.restrict (Set.Icc 0 t)) := (hIΨ.sub hIσ).abs.aestronglyMeasurable
          rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => abs_nonneg _) hm5]
          congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
          rw [he, Set.indicator_of_mem (show t - s ∈ Set.Ici 0 from by
            simp only [Set.mem_Ici]; linarith [hs.2])]
      _ ≤ (∫⁻ x, e (t - x) ∂H).toReal :=
          ENNReal.toReal_mono (ne_top_of_le_ne_top hrhs_top ht) (setLIntegral_le_lintegral _ _)
      _ ≤ (D * (∫⁻ v, e v) + ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono hrhs_top ht
      _ = D.toReal * (∫⁻ v, e v).toReal + ε / 2 := by
          rw [ENNReal.toReal_add (ENNReal.mul_ne_top hDtop hel_top) ENNReal.ofReal_ne_top,
            ENNReal.toReal_mul, ENNReal.toReal_ofReal (half_pos hε).le]
      _ ≤ D.toReal * η + ε / 2 := by
          gcongr
          exact ENNReal.toReal_le_of_le_ofReal hηpos.le hel
      _ ≤ ε := by
          have h0 : 0 ≤ (c + 1) * η := by positivity
          have e : (D.toReal + c + 1) * η = D.toReal * η + (c + 1) * η := by ring
          linarith

end SmithRegenerative.Equilibrium.RenewalLib

open MeasureTheory Filter Topology SmithRegenerative.Equilibrium in
theorem solution (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ)
    (hbdd : ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → |Ψ v| ≤ C)
    (hint : IntegrableOn Ψ (Set.Ioi 0))
    (hlim : Tendsto Ψ atTop (𝓝 0))
    (hS : InClassS F) (hμ : mean F < ⊤) :
    Tendsto (fun t : ℝ => ∫ s in Set.Icc 0 t, Ψ (t - s) ∂(renewalMeasure K F)) atTop
      (𝓝 ((K Set.univ).toReal / (mean F).toReal * ∫ v in Set.Ioi 0, Ψ v)) := by
  have h := RenewalLib.krt_spread F K hF hK Ψ hΨm hbdd hint hlim hS
  rw [ENNReal.toReal_inv, ← div_eq_mul_inv] at h
  exact h
