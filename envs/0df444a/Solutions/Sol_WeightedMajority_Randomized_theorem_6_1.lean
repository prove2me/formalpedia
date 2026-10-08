-- Prove2me | solution 1 for WeightedMajority.Randomized.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:47:43.625985+00:00
-- url     : https://prove2.me/submissions/da13ad56-f730-4ef9-b767-531582b9051d

import Mathlib
import Definitions.Def_WeightedMajority_Randomized_WMRModel

open MeasureTheory


namespace WeightedMajority.Randomized

lemma wmr_weight_nonneg {Ω : Type*} [MeasurableSpace Ω] {n t : ℕ} {β : ℝ} {w1 : Fin n → ℝ}
    {F : ℕ → Fin n → ℝ → ℝ → ℝ} {x : ℕ → Fin n → Ω → ℝ} {ρ lam : ℕ → Ω → ℝ}
    (hM : IsWMRModel t β w1 F x ρ lam) :
    ∀ j ≤ t, ∀ i ω, 0 ≤ weight w1 F x ρ j i ω := by
  obtain ⟨hb0, hb1, hw, -, -, -, -, -, -, -, hF⟩ := hM
  intro j
  induction j with
  | zero => intro _ i ω; simp [weight]; exact (hw i).le
  | succ j ih =>
    intro hj i ω
    simp only [weight]
    have h1 := (hF j (by omega) i ω).1
    have h2 : 0 ≤ β ^ |x j i ω - ρ j ω| := Real.rpow_nonneg hb0 _
    exact mul_nonneg (h2.trans h1) (ih (by omega) i ω)

lemma wmr_gamma_mem {Ω : Type*} [MeasurableSpace Ω] {n t : ℕ} {β : ℝ} {w1 : Fin n → ℝ}
    {F : ℕ → Fin n → ℝ → ℝ → ℝ} {x : ℕ → Fin n → Ω → ℝ} {ρ lam : ℕ → Ω → ℝ}
    (hM : IsWMRModel t β w1 F x ρ lam) {j : ℕ} (hj : j < t) (ω : Ω) :
    0 ≤ gamma w1 F x ρ j ω ∧ gamma w1 F x ρ j ω ≤ 1 := by
  have hw := wmr_weight_nonneg hM j hj.le
  have hx := hM.2.2.2.2.2.1
  have hs : 0 ≤ totalWeight w1 F x ρ j ω := Finset.sum_nonneg (fun i _ => hw i ω)
  unfold gamma
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · constructor
    · apply div_nonneg _ hs
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i ω) (hx j hj i ω).1)
    · rw [div_le_one hpos]
      unfold totalWeight
      exact Finset.sum_le_sum (fun i _ => by
        have := (hx j hj i ω).2
        nlinarith [hw i ω])

lemma wmr_history_le {Ω : Type*} [m0 : MeasurableSpace Ω] {n t : ℕ} {β : ℝ} {w1 : Fin n → ℝ}
    {F : ℕ → Fin n → ℝ → ℝ → ℝ} {x : ℕ → Fin n → Ω → ℝ} {ρ lam : ℕ → Ω → ℝ}
    (hM : IsWMRModel t β w1 F x ρ lam) {j : ℕ} (hj : j < t) :
    history x ρ j ≤ m0 := by
  obtain ⟨-, -, -, -, hx, -, hρ, -⟩ := hM
  refine iSup₂_le (fun k hk => ?_)
  apply Measurable.comap_le
  refine Measurable.prodMk ?_ (hρ k (by omega))
  exact measurable_pi_lambda _ (fun i => hx k (by omega) i)

lemma wmr_rho_meas {Ω : Type*} [m0 : MeasurableSpace Ω] {n : ℕ} (x : ℕ → Fin n → Ω → ℝ)
    (ρ : ℕ → Ω → ℝ) (j : ℕ) : Measurable[history x ρ j] (ρ j) := by
  have h : Measurable[MeasurableSpace.comap (fun ω => ((fun i => x j i ω), ρ j ω)) inferInstance]
      (ρ j) := by
    exact measurable_snd.comp (comap_measurable (fun ω => ((fun i => x j i ω), ρ j ω)))
  have hle : MeasurableSpace.comap (fun ω => ((fun i => x j i ω), ρ j ω)) inferInstance
      ≤ history x ρ j := le_iSup₂ (f := fun (k : ℕ) (_ : k ≤ j) =>
        MeasurableSpace.comap (fun ω => ((fun i => x k i ω), ρ k ω)) inferInstance) j le_rfl
  exact h.mono hle le_rfl

theorem em_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam) :
    (∀ j < t, P[fun ω => |lam j ω - ρ j ω| | history x ρ j]
        =ᵐ[P] fun ω => |gamma w1 F x ρ j ω - ρ j ω|) ∧
    ∫ ω, mistakes t lam ρ ω ∂P
      = ∫ ω, ∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω| ∂P := by
  obtain ⟨-, -, -, -, -, -, hρm, hρ01, hlm, hl01, -⟩ := id hM
  have key : ∀ j < t, (P[fun ω => |lam j ω - ρ j ω| | history x ρ j]
        =ᵐ[P] fun ω => |gamma w1 F x ρ j ω - ρ j ω|) ∧
        Integrable (fun ω => |lam j ω - ρ j ω|) P := by
    intro j hj
    have hle := wmr_history_le hM hj
    have hρmeas : Measurable (ρ j) := hρm j hj
    have hlmeas : Measurable (lam j) := hlm j hj
    have hρi : Integrable (ρ j) P := by
      refine Integrable.of_bound hρmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
      rcases hρ01 j hj ω with h | h <;> simp [h]
    have hli : Integrable (lam j) P := by
      refine Integrable.of_bound hlmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
      rcases hl01 j hj ω with h | h <;> simp [h]
    have hcm : Measurable (fun ω => 1 - 2 * ρ j ω) := by fun_prop
    have hci : Integrable (fun ω => 1 - 2 * ρ j ω) P := by
      refine Integrable.of_bound hcm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
      rcases hρ01 j hj ω with h | h <;> simp [h] <;> norm_num
    have hprod : Integrable ((fun ω => 1 - 2 * ρ j ω) * lam j) P := by
      refine Integrable.of_bound (hcm.mul hlmeas).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
      rcases hρ01 j hj ω with h | h <;> rcases hl01 j hj ω with h' | h' <;> simp [h, h'] <;> norm_num
    have hfeq : (fun ω => |lam j ω - ρ j ω|) = ρ j + (fun ω => 1 - 2 * ρ j ω) * lam j := by
      funext ω
      rcases hρ01 j hj ω with h | h <;> rcases hl01 j hj ω with h' | h' <;> simp [h, h'] <;> norm_num
    have hint : Integrable (fun ω => |lam j ω - ρ j ω|) P := by
      rw [hfeq]; exact hρi.add hprod
    refine ⟨?_, hint⟩
    have hρs : StronglyMeasurable[history x ρ j] (ρ j) := (wmr_rho_meas x ρ j).stronglyMeasurable
    have hcs : StronglyMeasurable[history x ρ j] (fun ω => 1 - 2 * ρ j ω) := by
      have : Measurable[history x ρ j] (fun ω => 1 - 2 * ρ j ω) := by
        have := wmr_rho_meas x ρ j
        fun_prop
      exact this.stronglyMeasurable
    rw [hfeq]
    have h1 := condExp_add hρi hprod (history x ρ j) (μ := P)
    have h2 := condExp_mul_of_stronglyMeasurable_left hcs hprod hli (μ := P)
    have h3 : P[ρ j | history x ρ j] = ρ j := condExp_of_stronglyMeasurable hle hρs hρi
    have h4 := hweak j hj
    filter_upwards [h1, h2, h4] with ω a b c
    rw [a]
    simp only [Pi.add_apply, h3]
    rw [b]
    simp only [Pi.mul_apply, c]
    obtain ⟨g0, g1⟩ := wmr_gamma_mem hM hj ω
    rcases hρ01 j hj ω with h | h <;> simp [h] <;> [rw [abs_of_nonneg g0]; rw [abs_of_nonpos (by linarith)]] <;> ring
  refine ⟨fun j hj => (key j hj).1, ?_⟩
  unfold mistakes
  rw [integral_finset_sum _ (fun j hj => (key j (Finset.mem_range.1 hj)).2)]
  have hle := fun j (hj : j < t) => wmr_history_le hM hj
  have e : ∀ j ∈ Finset.range t, ∫ ω, |lam j ω - ρ j ω| ∂P = ∫ ω, |gamma w1 F x ρ j ω - ρ j ω| ∂P := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [← integral_condExp (hle j hj') (μ := P) (f := fun ω => |lam j ω - ρ j ω|)]
    exact integral_congr_ae (key j hj').1
  rw [Finset.sum_congr rfl e, integral_finset_sum]
  intro j hj
  have hj' := Finset.mem_range.1 hj
  exact (integrable_condExp (μ := P) (m := history x ρ j) (f := fun ω => |lam j ω - ρ j ω|)).congr (key j hj').1


lemma wmr_step_le {Ω : Type*} [MeasurableSpace Ω] {n t : ℕ} {β : ℝ} {w1 : Fin n → ℝ}
    {F : ℕ → Fin n → ℝ → ℝ → ℝ} {x : ℕ → Fin n → Ω → ℝ} {ρ lam : ℕ → Ω → ℝ}
    (hM : IsWMRModel t β w1 F x ρ lam) {j : ℕ} (hj : j < t) (ω : Ω) :
    totalWeight w1 F x ρ (j+1) ω ≤ totalWeight w1 F x ρ j ω ∧
    (0 < totalWeight w1 F x ρ j ω →
      totalWeight w1 F x ρ (j+1) ω ≤
        totalWeight w1 F x ρ j ω * (1 - (1 - β) * |gamma w1 F x ρ j ω - ρ j ω|)) := by
  have hw := wmr_weight_nonneg hM j hj.le
  have hF := hM.2.2.2.2.2.2.2.2.2.2
  have hb1 := hM.2.1
  have hx := hM.2.2.2.2.2.1
  have hρ01 := hM.2.2.2.2.2.2.2.1
  have hs : totalWeight w1 F x ρ (j+1) ω =
      ∑ i, F j i (x j i ω) (ρ j ω) * weight w1 F x ρ j i ω := by
    simp [totalWeight, weight]
  constructor
  · rw [hs]
    unfold totalWeight
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h1 := (hF j hj i ω).2
    have h2 : 0 ≤ (1 - β) * |x j i ω - ρ j ω| := mul_nonneg (by linarith) (abs_nonneg _)
    have h3 : F j i (x j i ω) (ρ j ω) ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right h3 (hw i ω)
  · intro hpos
    have h1 : totalWeight w1 F x ρ (j+1) ω ≤
        totalWeight w1 F x ρ j ω - (1 - β) * ∑ i, weight w1 F x ρ j i ω * |x j i ω - ρ j ω| := by
      rw [hs]
      unfold totalWeight
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h1 := (hF j hj i ω).2
      nlinarith [hw i ω]
    have h2 : totalWeight w1 F x ρ j ω * |gamma w1 F x ρ j ω - ρ j ω| ≤
        ∑ i, weight w1 F x ρ j i ω * |x j i ω - ρ j ω| := by
      have e : totalWeight w1 F x ρ j ω * (gamma w1 F x ρ j ω - ρ j ω) =
          ∑ i, weight w1 F x ρ j i ω * (x j i ω - ρ j ω) := by
        unfold gamma
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_mul]
        unfold totalWeight
        rw [mul_div_cancel₀ _ (by unfold totalWeight at hpos; exact hpos.ne')]
      rw [← abs_of_pos hpos, ← abs_mul, e]
      calc _ ≤ ∑ i, |weight w1 F x ρ j i ω * (x j i ω - ρ j ω)| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [abs_mul, abs_of_nonneg (hw i ω)]
    have : 0 < 1 - β := by linarith
    nlinarith

lemma wmr_pointwise {Ω : Type*} [MeasurableSpace Ω] {n t : ℕ} {β : ℝ} {w1 : Fin n → ℝ}
    {F : ℕ → Fin n → ℝ → ℝ → ℝ} {x : ℕ → Fin n → Ω → ℝ} {ρ lam : ℕ → Ω → ℝ}
    (hM : IsWMRModel t β w1 F x ρ lam) (ω : Ω) (hfin : 0 < totalWeight w1 F x ρ t ω) :
    ∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω| ≤
      Real.log (totalWeight w1 F x ρ 0 ω / totalWeight w1 F x ρ t ω) / (1 - β) := by
  have hb1 := hM.2.1
  have hmono : ∀ d j, j + d ≤ t → totalWeight w1 F x ρ (j + d) ω ≤ totalWeight w1 F x ρ j ω := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j hjd
      have := (wmr_step_le hM (j := j + d) (by omega) ω).1
      have := ih j (by omega)
      rw [← add_assoc]; linarith
  have hpos : ∀ j ≤ t, 0 < totalWeight w1 F x ρ j ω := by
    intro j hj
    have := hmono (t - j) j (by omega)
    rw [show j + (t - j) = t by omega] at this
    linarith
  have hstep : ∀ j ∈ Finset.range t, (1 - β) * |gamma w1 F x ρ j ω - ρ j ω| ≤
      Real.log (totalWeight w1 F x ρ j ω) - Real.log (totalWeight w1 F x ρ (j+1) ω) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have p0 := hpos j hj'.le
    have p1 := hpos (j+1) hj'
    have h := (wmr_step_le hM hj' ω).2 p0
    set a := |gamma w1 F x ρ j ω - ρ j ω|
    set r := 1 - (1 - β) * a
    have hr : totalWeight w1 F x ρ (j+1) ω / totalWeight w1 F x ρ j ω ≤ r := by
      rw [div_le_iff₀ p0]; linarith
    have hrpos : 0 < r := lt_of_lt_of_le (div_pos p1 p0) hr
    have hlog : Real.log (totalWeight w1 F x ρ (j+1) ω / totalWeight w1 F x ρ j ω) ≤ r - 1 :=
      (Real.log_le_log (div_pos p1 p0) hr).trans (Real.log_le_sub_one_of_pos hrpos)
    rw [Real.log_div p1.ne' p0.ne'] at hlog
    simp only [r] at hlog
    linarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub'] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [Real.log_div (hpos 0 (Nat.zero_le _)).ne' hfin.ne', le_div_iff₀ (by linarith), mul_comm]
  exact hsum

theorem goal_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam)
    (hfin : ∀ᵐ ω ∂P, 0 < totalWeight w1 F x ρ t ω) :
    ∫⁻ ω, ENNReal.ofReal (mistakes t lam ρ ω) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal
          (Real.log (totalWeight w1 F x ρ 0 ω / totalWeight w1 F x ρ t ω)) ∂P)
        / ENNReal.ofReal (1 - β) := by
  have hb1 := hM.2.1
  have hlm := hM.2.2.2.2.2.2.2.2.1
  have hρm := hM.2.2.2.2.2.2.1
  have hρ01 := hM.2.2.2.2.2.2.2.1
  have hl01 := hM.2.2.2.2.2.2.2.2.2.1
  have hmeas : Measurable (mistakes t lam ρ) := by
    unfold mistakes
    refine Finset.measurable_sum _ (fun j hj => ?_)
    have hj' := Finset.mem_range.1 hj
    exact ((hlm j hj').sub (hρm j hj')).abs
  have hint : Integrable (mistakes t lam ρ) P := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (t : ℝ) (Filter.Eventually.of_forall fun ω => ?_)
    unfold mistakes
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
    calc _ ≤ ∑ j ∈ Finset.range t, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hj' := Finset.mem_range.1 hj
          rcases hρ01 j hj' ω with h | h <;> rcases hl01 j hj' ω with h' | h' <;> simp [h, h']
      _ = t := by simp
  have hnn : 0 ≤ᵐ[P] mistakes t lam ρ :=
    Filter.Eventually.of_forall fun ω => Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have e1 : ENNReal.ofReal (∫ ω, mistakes t lam ρ ω ∂P) = ∫⁻ ω, ENNReal.ofReal (mistakes t lam ρ ω) ∂P :=
    ofReal_integral_eq_lintegral_ofReal hint hnn
  have e2 := (em_core P β w1 F x ρ lam hM hweak).2
  have h3 : ENNReal.ofReal (∫ ω, ∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω| ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal (∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω|) ∂P := by
    by_cases hi : Integrable (fun ω => ∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω|) P
    · rw [ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg (fun j _ => abs_nonneg _))]
    · rw [integral_undef hi]; simp
  have hpos1 : (0 : ℝ) < 1 - β := by linarith
  have h4 : ∫⁻ ω, ENNReal.ofReal (∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω|) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (Real.log (totalWeight w1 F x ρ 0 ω / totalWeight w1 F x ρ t ω))
        * (ENNReal.ofReal (1 - β))⁻¹ ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hfin] with ω hω
    rw [← ENNReal.ofReal_inv_of_pos hpos1, ← ENNReal.ofReal_mul' (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_mul_inv]
    exact wmr_pointwise hM ω hω
  rw [div_eq_mul_inv, ← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (by simpa using hpos1))]
  rw [← e1, e2]
  exact h3.trans h4

end WeightedMajority.Randomized

open WeightedMajority.Randomized


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam)
    (hfin : ∀ᵐ ω ∂P, 0 < totalWeight w1 F x ρ t ω) :
    ∫⁻ ω, ENNReal.ofReal (mistakes t lam ρ ω) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal
          (Real.log (totalWeight w1 F x ρ 0 ω / totalWeight w1 F x ρ t ω)) ∂P)
        / ENNReal.ofReal (1 - β) := by
  exact goal_core P β w1 F x ρ lam hM hweak hfin
