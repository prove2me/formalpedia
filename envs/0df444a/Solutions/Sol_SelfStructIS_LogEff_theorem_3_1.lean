-- Prove2me | solution 1 for SelfStructIS.LogEff.theorem_3_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:54:02.357417+00:00
-- url     : https://prove2.me/submissions/7d39e4cc-7eb6-456a-8a17-6185d16567ac

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SSIS31D

/-- Main part of the (unnormalised) density: `e^{-z₀} (1 + z₁²)⁻¹`. -/
noncomputable def A (z : Fin 2 → ℝ) : ℝ := Real.exp (-z 0) * (1 + z 1 ^ 2)⁻¹

/-- The leak region `z₀² ≤ z₁`. -/
def R : Set (Fin 2 → ℝ) := {z | z 0 ^ 2 ≤ z 1}

/-- Leak density `(1 + z₁)⁻¹ (1 + z₁²)⁻¹`. -/
noncomputable def B (z : Fin 2 → ℝ) : ℝ := (1 + z 1)⁻¹ * (1 + z 1 ^ 2)⁻¹

noncomputable def g (z : Fin 2 → ℝ) : ℝ := A z + R.indicator B z

def P : Set (Fin 2 → ℝ) := {z | ∀ i, 0 ≤ z i}

noncomputable def h (z : Fin 2 → ℝ) : ℝ := P.indicator g z

noncomputable def H (z : Fin 2 → ℝ) : ℝ := ∏ i, (1 + z i ^ 2)⁻¹

lemma A_pos (z : Fin 2 → ℝ) : 0 < A z := by unfold A; positivity

lemma B_nonneg (z : Fin 2 → ℝ) (hz : z ∈ P) : 0 ≤ B z := by
  have := hz 1
  unfold B; positivity

lemma ind_nonneg (z : Fin 2 → ℝ) (hz : z ∈ P) : 0 ≤ R.indicator B z := by
  by_cases hR : z ∈ R
  · rw [Set.indicator_of_mem hR]; exact B_nonneg z hz
  · rw [Set.indicator_of_notMem hR]

lemma g_ge_A (z : Fin 2 → ℝ) (hz : z ∈ P) : A z ≤ g z := by
  unfold g; linarith [ind_nonneg z hz]

lemma g_pos (z : Fin 2 → ℝ) (hz : z ∈ P) : 0 < g z := lt_of_lt_of_le (A_pos z) (g_ge_A z hz)

lemma A_le_one (z : Fin 2 → ℝ) (hz : z ∈ P) : A z ≤ 1 := by
  unfold A
  have h0 := hz 0
  have h1 : Real.exp (-z 0) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : (1 + z 1 ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  calc Real.exp (-z 0) * (1 + z 1 ^ 2)⁻¹ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = 1 := one_mul 1

lemma B_le_one (z : Fin 2 → ℝ) (hz : z ∈ P) : B z ≤ 1 := by
  unfold B
  have h1 := hz 1
  have h2 : (1 + z 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h3 : (1 + z 1 ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  calc (1 + z 1)⁻¹ * (1 + z 1 ^ 2)⁻¹ ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) zero_le_one
    _ = 1 := one_mul 1

lemma g_le_two (z : Fin 2 → ℝ) (hz : z ∈ P) : g z ≤ 2 := by
  unfold g
  have := A_le_one z hz
  have : R.indicator B z ≤ 1 := by
    by_cases hR : z ∈ R
    · rw [Set.indicator_of_mem hR]; exact B_le_one z hz
    · rw [Set.indicator_of_notMem hR]; norm_num
  linarith

lemma g_eq_A (z : Fin 2 → ℝ) (hR : z ∉ R) : g z = A z := by
  unfold g; rw [Set.indicator_of_notMem hR, add_zero]

lemma H_nonneg (z : Fin 2 → ℝ) : 0 ≤ H z := by unfold H; positivity

lemma h_le_H (z : Fin 2 → ℝ) : h z ≤ 3 * H z := by
  unfold h
  by_cases hz : z ∈ P
  · rw [Set.indicator_of_mem hz]
    have hH : H z = (1 + z 0 ^ 2)⁻¹ * (1 + z 1 ^ 2)⁻¹ := by
      unfold H; rw [Fin.prod_univ_two]
    have h0 := hz 0
    have h1 := hz 1
    have hA : A z ≤ 2 * H z := by
      unfold A
      rw [hH]
      have hexp : Real.exp (-z 0) ≤ 2 * (1 + z 0 ^ 2)⁻¹ := by
        have hq := Real.quadratic_le_exp_of_nonneg h0
        rw [Real.exp_neg, inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _)
          (by positivity)]
        nlinarith
      calc Real.exp (-z 0) * (1 + z 1 ^ 2)⁻¹ ≤ 2 * (1 + z 0 ^ 2)⁻¹ * (1 + z 1 ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hexp (by positivity)
        _ = _ := by ring
    have hB : R.indicator B z ≤ H z := by
      by_cases hR : z ∈ R
      · rw [Set.indicator_of_mem hR, hH]
        unfold B
        have hR' : z 0 ^ 2 ≤ z 1 := hR
        have : (1 + z 1)⁻¹ ≤ (1 + z 0 ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (by linarith)
        exact mul_le_mul_of_nonneg_right this (by positivity)
      · rw [Set.indicator_of_notMem hR]; exact H_nonneg z
    unfold g; linarith
  · rw [Set.indicator_of_notMem hz]; linarith [H_nonneg z]

lemma H_integrable : Integrable H (volume : Measure (Fin 2 → ℝ)) := by
  have := Integrable.fintype_prod (ι := Fin 2) (f := fun _ (x : ℝ) => (1 + x ^ 2)⁻¹)
    (μ := fun _ => (volume : Measure ℝ)) (fun _ => integrable_inv_one_add_sq)
  exact this

lemma Z_lt_top : ∫⁻ z, ENNReal.ofReal (h z) < ⊤ := by
  have hi : Integrable (fun z => 3 * H z) (volume : Measure (Fin 2 → ℝ)) := H_integrable.const_mul 3
  calc ∫⁻ z, ENNReal.ofReal (h z) ≤ ∫⁻ z, ENNReal.ofReal (3 * H z) :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (h_le_H z)
    _ < ⊤ := hi.lintegral_lt_top

lemma Z_pos : 0 < ∫⁻ z, ENNReal.ofReal (h z) := by
  set box := Set.Icc (0 : Fin 2 → ℝ) 1 with hbox
  have hvol : volume box = 1 := by rw [hbox, Real.volume_Icc_pi]; simp
  have hlow : ∀ z ∈ box, ENNReal.ofReal (Real.exp (-1) * 2⁻¹) ≤ ENNReal.ofReal (h z) := by
    intro z hz
    have hP : z ∈ P := fun i => hz.1 i
    apply ENNReal.ofReal_le_ofReal
    unfold h; rw [Set.indicator_of_mem hP]
    refine le_trans ?_ (g_ge_A z hP)
    unfold A
    have h0 : z 0 ≤ 1 := hz.2 0
    have h1 : z 1 ≤ 1 := hz.2 1
    have h1' : 0 ≤ z 1 := hz.1 1
    apply mul_le_mul (Real.exp_le_exp.2 (by linarith)) _ (by positivity) (by positivity)
    exact inv_anti₀ (by positivity) (by nlinarith)
  calc (0 : ENNReal) < ENNReal.ofReal (Real.exp (-1) * 2⁻¹) := by
        rw [ENNReal.ofReal_pos]; positivity
    _ = ∫⁻ _ in box, ENNReal.ofReal (Real.exp (-1) * 2⁻¹) := by
        rw [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ z in box, ENNReal.ofReal (h z) := setLIntegral_mono' measurableSet_Icc hlow
    _ ≤ _ := setLIntegral_le_lintegral _ _

end SSIS31D

namespace SSIS31D

lemma log_div_nat : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  refine (h.comp h2).congr (fun n => ?_)
  simp only [Function.comp, pow_one]
  congr 1; ring

lemma logterm (ys : ℕ → Fin 2 → ℝ) (C : ℝ) (hC : ∀ n, |ys n 1| ≤ C) :
    Tendsto (fun n : ℕ => Real.log (1 + ((n : ℝ) * ys n 1) ^ 2) / n) atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hup : Tendsto (fun n : ℕ => Real.log (1 + C ^ 2) / n + 2 * (Real.log ((n : ℝ) + 1) / n))
      atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log (1 + C ^ 2))).add
      (log_div_nat.const_mul 2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
  · exact div_nonneg (Real.log_nonneg (by nlinarith)) (Nat.cast_nonneg n)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : 1 + ((n : ℝ) * ys n 1) ^ 2 ≤ (1 + C ^ 2) * ((n : ℝ) + 1) ^ 2 := by
      have h1 : ((n : ℝ) * ys n 1) ^ 2 ≤ ((n : ℝ) * C) ^ 2 := by
        rw [mul_pow, mul_pow]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := hC n
        nlinarith [abs_nonneg (ys n 1), sq_abs (ys n 1)]
      nlinarith
    have hlog : Real.log (1 + ((n : ℝ) * ys n 1) ^ 2) ≤
        Real.log (1 + C ^ 2) + 2 * Real.log ((n : ℝ) + 1) := by
      calc Real.log (1 + ((n : ℝ) * ys n 1) ^ 2) ≤ Real.log ((1 + C ^ 2) * ((n : ℝ) + 1) ^ 2) :=
            Real.log_le_log (by positivity) hle
        _ = _ := by rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
    calc Real.log (1 + ((n : ℝ) * ys n 1) ^ 2) / n
        ≤ (Real.log (1 + C ^ 2) + 2 * Real.log ((n : ℝ) + 1)) / n :=
          div_le_div_of_nonneg_right hlog hn'.le
      _ = _ := by ring

end SSIS31D

namespace SSIS31D

noncomputable def Z : ENNReal := ∫⁻ z, ENNReal.ofReal (h z)

noncomputable def c : ℝ := (Z.toReal)⁻¹

noncomputable def pp (z : Fin 2 → ℝ) : ℝ := P.indicator (fun _ => c) z

noncomputable def φφ (z : Fin 2 → ℝ) : ℝ := -Real.log (g z)

def II (z : Fin 2 → ℝ) : ℝ := z 0

lemma Zr_pos : 0 < Z.toReal := ENNReal.toReal_pos Z_pos.ne' Z_lt_top.ne

lemma c_pos : 0 < c := inv_pos.2 Zr_pos

lemma dens (z : Fin 2 → ℝ) : pp z * Real.exp (-φφ z) = c * h z := by
  unfold pp φφ h
  by_cases hz : z ∈ P
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, neg_neg, Real.exp_log (g_pos z hz)]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; simp

lemma negLogA (z : Fin 2 → ℝ) : -Real.log (A z) = z 0 + Real.log (1 + z 1 ^ 2) := by
  unfold A
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_inv]; ring

lemma conv : SelfStructIS.LogEff.Conv13 pp φφ II := by
  intro ys y hys0 hys hy
  have hzP : ∀ n : ℕ, (n : ℝ) • ys n ∈ P := fun n i => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (Nat.cast_nonneg n) (hys0 n i)
  refine ⟨?_, Eventually.of_forall fun n => ?_, fun ε hε => ?_⟩
  · obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto ys hys).exists_norm_le
    have hC1 : ∀ n, |ys n 1| ≤ C := fun n => by
      have := hC (ys n) ⟨n, rfl⟩
      exact le_trans (by simpa using norm_le_pi_norm (ys n) 1) this
    have hT := logterm ys C hC1
    have hy0 : Tendsto (fun n => ys n 0) atTop (𝓝 (y 0)) := ((continuous_apply 0).tendsto y).comp hys
    have hU : Tendsto (fun n : ℕ => ys n 0 + Real.log (1 + ((n : ℝ) * ys n 1) ^ 2) / n) atTop
        (𝓝 (y 0)) := by simpa using hy0.add hT
    have hz0 : ∀ n : ℕ, ((n : ℝ) • ys n) 0 = n * ys n 0 := fun n => by simp
    have hz1 : ∀ n : ℕ, ((n : ℝ) • ys n) 1 = n * ys n 1 := fun n => by simp
    have hexact : ∀ n : ℕ, 1 ≤ n → (n : ℝ) • ys n ∉ R →
        φφ ((n : ℝ) • ys n) / n = ys n 0 + Real.log (1 + ((n : ℝ) * ys n 1) ^ 2) / n := by
      intro n hn hR
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      unfold φφ
      rw [g_eq_A _ hR, negLogA, hz0, hz1]
      field_simp
    have hupper : ∀ n : ℕ, 1 ≤ n →
        φφ ((n : ℝ) • ys n) / n ≤ ys n 0 + Real.log (1 + ((n : ℝ) * ys n 1) ^ 2) / n := by
      intro n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hle : φφ ((n : ℝ) • ys n) ≤ -Real.log (A ((n : ℝ) • ys n)) := by
        unfold φφ
        have := Real.log_le_log (A_pos _) (g_ge_A _ (hzP n))
        linarith
      rw [negLogA, hz0, hz1] at hle
      calc φφ ((n : ℝ) • ys n) / n ≤ (n * ys n 0 + Real.log (1 + ((n : ℝ) * ys n 1) ^ 2)) / n :=
            div_le_div_of_nonneg_right hle hn'.le
        _ = _ := by field_simp
    have hy00 : 0 ≤ y 0 := ge_of_tendsto' hy0 (fun n => hys0 n 0)
    show Tendsto (fun n : ℕ => φφ ((n : ℝ) • ys n) / n) atTop (𝓝 (y 0))
    rcases hy00.lt_or_eq with hpos | hzero
    · -- eventually outside the leak region
      have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) • ys n ∉ R := by
        have h1 := hy0.eventually (lt_mem_nhds (show y 0 / 2 < y 0 by linarith))
        obtain ⟨M, hM⟩ := exists_nat_gt (4 * C / (y 0) ^ 2)
        filter_upwards [h1, eventually_gt_atTop M] with n hn1 hn2
        intro hR
        have hR' : ((n : ℝ) • ys n) 0 ^ 2 ≤ ((n : ℝ) • ys n) 1 := hR
        rw [hz0, hz1] at hR'
        have hnM : (M : ℝ) < n := by exact_mod_cast hn2
        have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (Nat.cast_nonneg M) hnM
        have hys1 : ys n 1 ≤ C := le_trans (le_abs_self _) (hC1 n)
        have hsq : (y 0 / 2) ^ 2 < ys n 0 ^ 2 := by
          have : 0 < y 0 / 2 := by linarith
          nlinarith
        have h4 : 4 * C < n * (y 0) ^ 2 := by
          rw [div_lt_iff₀ (by positivity)] at hM
          have : (M : ℝ) * y 0 ^ 2 < n * y 0 ^ 2 := mul_lt_mul_of_pos_right hnM (by positivity)
          linarith
        have : (n : ℝ) * ys n 0 ^ 2 ≤ ys n 1 := by
          have : (n : ℝ) * ((n : ℝ) * ys n 0 ^ 2) ≤ n * ys n 1 := by nlinarith
          exact le_of_mul_le_mul_left this hnpos
        nlinarith
      refine hU.congr' ?_
      filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
      exact (hexact n hn1 hn).symm
    · -- y 0 = 0: squeeze
      rw [← hzero] at hU ⊢
      have hlow : Tendsto (fun n : ℕ => -Real.log 2 / n) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hU ?_ ?_
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        apply div_le_div_of_nonneg_right _ hn'.le
        unfold φφ
        have := Real.log_le_log (g_pos _ (hzP n)) (g_le_two _ (hzP n))
        linarith
      · filter_upwards [eventually_ge_atTop 1] with n hn
        exact hupper n hn
  · show 0 < pp ((n : ℝ) • ys n)
    unfold pp; rw [Set.indicator_of_mem (hzP n)]; exact c_pos
  · have : (fun n : ℕ => Real.log (pp ((n : ℝ) • ys n)) / (n : ℝ) ^ ε) =
        fun n : ℕ => Real.log c / (n : ℝ) ^ ε := funext fun n => by
      unfold pp; rw [Set.indicator_of_mem (hzP n)]
    rw [this]
    exact tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop)

end SSIS31D

namespace SSIS31D

open SelfStructIS.LogEff

noncomputable def νν : Measure (Fin 2 → ℝ) :=
  volume.withDensity (fun y => ENNReal.ofReal (pp y * Real.exp (-φφ y)))

lemma dens' : (fun y => ENNReal.ofReal (pp y * Real.exp (-φφ y))) =
    fun y => ENNReal.ofReal c * ENNReal.ofReal (h y) := by
  funext y; rw [dens, ENNReal.ofReal_mul c_pos.le]

instance : IsProbabilityMeasure νν := by
  constructor
  rw [νν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, dens',
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change ENNReal.ofReal c * Z = 1
  rw [← ENNReal.ofReal_toReal (show Z ≠ ⊤ from Z_lt_top.ne), ← ENNReal.ofReal_mul c_pos.le, c,
    inv_mul_cancel₀ Zr_pos.ne', ENNReal.ofReal_one]

lemma P_meas : MeasurableSet {y : Fin 2 → ℝ | ∀ i, 0 ≤ y i} := by
  have : {y : Fin 2 → ℝ | ∀ i, 0 ≤ y i} = ⋂ i, {y : Fin 2 → ℝ | 0 ≤ y i} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)

lemma supp : νν {y : Fin 2 → ℝ | ∀ i, 0 ≤ y i}ᶜ = 0 := by
  rw [νν, withDensity_apply _ P_meas.compl]
  apply le_antisymm _ bot_le
  calc ∫⁻ y in {y : Fin 2 → ℝ | ∀ i, 0 ≤ y i}ᶜ, ENNReal.ofReal (pp y * Real.exp (-φφ y))
      ≤ ∫⁻ _ in {y : Fin 2 → ℝ | ∀ i, 0 ≤ y i}ᶜ, 0 := by
        refine setLIntegral_mono' P_meas.compl fun y hy => ?_
        have hy' : y ∉ P := hy
        unfold pp; rw [Set.indicator_of_notMem hy']; simp
    _ = 0 := lintegral_zero

lemma not_ldp : ¬ IsLDP (fun t : ℝ => νν.map (fun y => t⁻¹ • y)) (rateExt II) := by
  rintro ⟨hU, -⟩
  set F := {y : Fin 2 → ℝ | 1 ≤ y 0} with hFdef
  have hF : IsClosed F := isClosed_le continuous_const (continuous_apply 0)
  have h1 := hU F hF
  have hinf : (1 : EReal) ≤ ⨅ x ∈ F, rateExt II x := by
    refine le_iInf₂ fun x hx => ?_
    unfold rateExt
    split_ifs
    · have : (1 : ℝ) ≤ II x := hx
      exact_mod_cast this
    · exact le_top
  -- the rate along the leak
  set r : ℝ → ℝ := fun t => t⁻¹ * Real.log c - 6 * (Real.log (t + 2) / t) with hr
  have hr_t : Tendsto r atTop (𝓝 0) := by
    have e1 : Tendsto (fun t : ℝ => t⁻¹ * Real.log c) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.mul_const (Real.log c)
    have e2 : Tendsto (fun t : ℝ => Real.log (t + 2) / t) atTop (𝓝 0) := by
      have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero
      refine (h.comp (tendsto_atTop_add_const_right _ 2 tendsto_id)).congr (fun t => ?_)
      simp only [Function.comp, id, pow_one]
      congr 1; ring
    have := e1.sub (e2.const_mul 6)
    simpa using this
  have hlow : ∀ᶠ t : ℝ in atTop, (((-1 / 2 : ℝ)) : EReal) ≤
      ((t⁻¹ : ℝ) : EReal) * ENNReal.log ((νν.map (fun y => t⁻¹ • y)) F) := by
    filter_upwards [hr_t.eventually (lt_mem_nhds (show (-1 / 2 : ℝ) < 0 by norm_num)),
      eventually_ge_atTop 1] with t hrt ht1
    have ht : 0 < t := by linarith
    have hmeas : Measurable (fun y : Fin 2 → ℝ => t⁻¹ • y) := by fun_prop
    rw [Measure.map_apply hmeas hF.measurableSet]
    set L := c * ((t + 2) ^ 6)⁻¹ with hL
    have hLpos : 0 < L := mul_pos c_pos (by positivity)
    set box := Set.Icc (![t, (t + 1) ^ 2] : Fin 2 → ℝ) ![t + 1, (t + 1) ^ 2 + 1] with hbox
    have hvol : volume box = 1 := by
      rw [hbox, Real.volume_Icc_pi]; simp [Fin.prod_univ_two]
    have hdens : ∀ z ∈ box, ENNReal.ofReal L ≤ ENNReal.ofReal (pp z * Real.exp (-φφ z)) := by
      intro z hz
      have hz0 : t ≤ z 0 := by simpa using hz.1 0
      have hz0' : z 0 ≤ t + 1 := by simpa using hz.2 0
      have hz1 : (t + 1) ^ 2 ≤ z 1 := by simpa using hz.1 1
      have hz1' : z 1 ≤ (t + 1) ^ 2 + 1 := by simpa using hz.2 1
      have hP : z ∈ P := by
        intro i; fin_cases i
        · simp; linarith
        · simp; nlinarith
      have hR : z ∈ R := by
        show z 0 ^ 2 ≤ z 1
        have : z 0 ^ 2 ≤ (t + 1) ^ 2 := pow_le_pow_left₀ (by linarith) hz0' 2
        linarith
      rw [dens]
      apply ENNReal.ofReal_le_ofReal
      unfold h; rw [Set.indicator_of_mem hP]
      apply mul_le_mul_of_nonneg_left _ c_pos.le
      have hB : ((t + 2) ^ 6)⁻¹ ≤ B z := by
        unfold B
        rw [← mul_inv]
        apply inv_anti₀ (by have := hP 1; positivity)
        have hz1pos : 0 ≤ z 1 := hP 1
        have e1 : 1 + z 1 ≤ (t + 2) ^ 2 := by nlinarith
        have e2 : 1 + z 1 ^ 2 ≤ (t + 2) ^ 4 := by
          have : z 1 ^ 2 + 1 ≤ ((t + 2) ^ 2) ^ 2 := by nlinarith
          nlinarith
        calc (1 + z 1) * (1 + z 1 ^ 2) ≤ (t + 2) ^ 2 * (t + 2) ^ 4 :=
              mul_le_mul e1 e2 (by positivity) (by positivity)
          _ = (t + 2) ^ 6 := by ring
      unfold g; rw [Set.indicator_of_mem hR]
      linarith [A_pos z]
    have hbox_le : ENNReal.ofReal L ≤ νν box := by
      rw [νν, withDensity_apply _ measurableSet_Icc]
      calc ENNReal.ofReal L = ∫⁻ _ in box, ENNReal.ofReal L := by
            rw [setLIntegral_const, hvol, mul_one]
        _ ≤ _ := setLIntegral_mono' measurableSet_Icc hdens
    have hsub : box ⊆ (fun y : Fin 2 → ℝ => t⁻¹ • y) ⁻¹' F := by
      intro z hz
      have hz0 : t ≤ z 0 := by simpa using hz.1 0
      show 1 ≤ (t⁻¹ • z) 0
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [le_inv_mul_iff₀ ht]; linarith
    have hmono := le_trans hbox_le (measure_mono hsub)
    have hlog := ENNReal.log_le_log hmono
    rw [ENNReal.log_ofReal_of_pos hLpos] at hlog
    have hmul : ((t⁻¹ : ℝ) : EReal) * ((Real.log L : ℝ) : EReal) ≤
        ((t⁻¹ : ℝ) : EReal) * ENNReal.log (νν ((fun y : Fin 2 → ℝ => t⁻¹ • y) ⁻¹' F)) :=
      mul_le_mul_of_nonneg_left hlog (EReal.coe_nonneg.2 (inv_nonneg.2 ht.le))
    refine le_trans ?_ hmul
    rw [← EReal.coe_mul]
    apply EReal.coe_le_coe_iff.2
    have : t⁻¹ * Real.log L = r t := by
      rw [hL, Real.log_mul c_pos.ne' (by positivity), Real.log_inv, Real.log_pow, hr]
      field_simp
      push_cast; ring
    rw [this]; linarith
  have h2 := le_limsup_of_frequently_le' hlow.frequently
  have h3 : -(⨅ x ∈ F, rateExt II x) ≤ -1 := EReal.neg_le_neg_iff.2 hinf
  have h4 := le_trans (le_trans h2 h1) h3
  have : ((-1 / 2 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := by simpa using h4
  rw [EReal.coe_le_coe_iff] at this
  norm_num at this

end SSIS31D

open SelfStructIS.LogEff in
theorem solution : ¬ (∀ (d : ℕ) (hd : 0 < d) (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (p φ I : (Fin d → ℝ) → ℝ)
    (hdens : ν = volume.withDensity (fun y => ENNReal.ofReal (p y * Real.exp (-φ y))))
    (hsupp : ν {y | ∀ i, 0 ≤ y i}ᶜ = 0)
    (hI : ∀ y : Fin d → ℝ, (∀ i, 0 ≤ y i) → 0 ≤ I y)
    (h13 : Conv13 p φ I),
    IsLDP (fun t : ℝ => ν.map (fun y => t⁻¹ • y)) (rateExt I)) := by
  intro hall
  exact SSIS31D.not_ldp (hall 2 two_pos SSIS31D.νν SSIS31D.pp SSIS31D.φφ SSIS31D.II rfl
    SSIS31D.supp (fun y hy => hy 0) SSIS31D.conv)
