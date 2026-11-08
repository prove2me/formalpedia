-- Prove2me | solution 1 for RegretBandits.Adversarial.exp3P_expected_regret
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:08:20.38304+00:00
-- url     : https://prove2.me/submissions/1471c1c6-8d51-4bb9-8844-8c5d8580fb18

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3P
import Theorems.Thm_RegretBandits_Adversarial_exp3P_high_prob_regret_any_conf

open MeasureTheory
open RegretBandits.Adversarial

/-- The regret is a measurable function of `ω` (it depends on `I 1 ω, …, I n ω` only). -/
lemma regret_measurable_aux {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (g : Adversary K)
    {Ω : Type*} [MeasurableSpace Ω] (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) :
    Measurable (fun ω => regret g n I ω) := by
  let d : Fin K := ⟨0, by omega⟩
  let ext : (Fin (n + 1) → Fin K) → (ℕ → Fin K) :=
    fun r s => if hs : s < n + 1 then r ⟨s, hs⟩ else d
  let F : (ℕ → Fin K) → ℝ := fun h =>
    (⨆ i : Fin K, ∑ t ∈ Finset.Icc 1 n, g.val t h i) -
      ∑ t ∈ Finset.Icc 1 n, g.val t h (h t)
  have hF : ∀ h : ℕ → Fin K, F h = F (ext (fun s => h s)) := by
    intro h
    have hval : ∀ t ∈ Finset.Icc 1 n, g.val t h = g.val t (ext (fun s => h s)) := by
      intro t ht
      apply g.nonanticipating
      intro s _ hst
      have : s < n + 1 := by simp at ht; omega
      show h s = (if hs : s < n + 1 then h s else d)
      rw [dif_pos this]
    have hpt : ∀ t ∈ Finset.Icc 1 n, h t = ext (fun s => h s) t := by
      intro t ht
      have : t < n + 1 := by simp at ht; omega
      show h t = (if hs : t < n + 1 then h t else d)
      rw [dif_pos this]
    simp only [F]
    congr 1
    · congr 1
      funext i
      exact Finset.sum_congr rfl (fun t ht => by rw [hval t ht])
    · exact Finset.sum_congr rfl (fun t ht => by rw [hval t ht, ← hpt t ht])
  have hmeasR : Measurable (fun ω => (fun s : Fin (n + 1) => I s ω)) :=
    measurable_pi_lambda _ (fun s => hI s)
  have hFm : Measurable (fun r : Fin (n + 1) → Fin K => F (ext r)) := measurable_of_countable _
  have : (fun ω => regret g n I ω) = (fun r => F (ext r)) ∘ (fun ω => (fun s : Fin (n + 1) => I s ω)) := by
    funext ω
    exact hF (fun s => I s ω)
  rw [this]
  exact hFm.comp hmeasR

lemma regret_abs_le_aux {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (g : Adversary K)
    {Ω : Type*} (I : ℕ → Ω → Fin K) (ω : Ω) :
    |regret g n I ω| ≤ 2 * n := by
  have hne : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  have hb : ∀ i, ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i ≤ n := by
    intro i
    calc ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i ≤ ∑ t ∈ Finset.Icc 1 n, (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ => (g.val_mem _ _ _).2)
      _ = n := by simp
  have hb0 : ∀ i, 0 ≤ ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i :=
    fun i => Finset.sum_nonneg (fun t _ => (g.val_mem _ _ _).1)
  have hbdd : BddAbove (Set.range fun i : Fin K => ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i) :=
    Set.finite_range _ |>.bddAbove
  have h1 : (⨆ i : Fin K, ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i) ≤ n := ciSup_le hb
  have h2 : 0 ≤ (⨆ i : Fin K, ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i) :=
    le_trans (hb0 ⟨0, by omega⟩) (le_ciSup hbdd _)
  have h3 : ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) (I t ω) ≤ n := by
    calc ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) (I t ω) ≤ ∑ t ∈ Finset.Icc 1 n, (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ => (g.val_mem _ _ _).2)
      _ = n := by simp
  have h4 : 0 ≤ ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) (I t ω) :=
    Finset.sum_nonneg (fun t _ => (g.val_mem _ _ _).1)
  unfold regret
  rw [abs_le]
  constructor <;> linarith

theorem solution {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n) (g : Adversary K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K)
    (hI : IsRun P
      (exp3PProb (Real.sqrt (Real.log K / (n * K)))
        (1.05 * Real.sqrt (K * Real.log K / n))
        (0.95 * Real.sqrt (Real.log K / (n * K))) g) I) :
    ∫ ω, regret g n I ω ∂P ≤
      5.15 * Real.sqrt (n * K * Real.log K) + Real.sqrt (n * K / Real.log K) := by
  set a : ℝ := 5.15 * Real.sqrt (n * K * Real.log K) with ha
  set b : ℝ := Real.sqrt (n * K / Real.log K) with hb
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog : 0 < Real.log K := Real.log_pos (by linarith)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbpos : 0 < b := Real.sqrt_pos.2 (div_pos (by positivity) hlog)
  set R : Ω → ℝ := fun ω => regret g n I ω with hR
  have hRm : Measurable R := regret_measurable_aux hK n g I hI.1
  have hRb : ∀ ω, |R ω| ≤ 2 * n := fun ω => regret_abs_le_aux hK n g I ω
  have hRint : Integrable R P :=
    Integrable.of_bound hRm.aestronglyMeasurable (2 * n) (Filter.Eventually.of_forall hRb)
  set X : Ω → ℝ := fun ω => max 0 ((R ω - a) / b) with hX
  have hXm : Measurable X := by
    exact measurable_const.max ((hRm.sub measurable_const).div_const b)
  have hXint : Integrable X P := by
    refine Integrable.of_bound hXm.aestronglyMeasurable ((2 * n + |a|) / b)
      (Filter.Eventually.of_forall (fun ω => ?_))
    have h1 := hRb ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    apply max_le (by positivity)
    apply div_le_div_of_nonneg_right _ hbpos.le
    have := le_abs_self (R ω)
    have := neg_abs_le a
    linarith
  have hRle : ∀ ω, R ω ≤ a + b * X ω := by
    intro ω
    have : (R ω - a) / b ≤ X ω := le_max_right _ _
    have h2 : R ω - a ≤ b * X ω := by
      rw [div_le_iff₀ hbpos] at this; linarith
    linarith
  -- tail bound
  have htail : ∀ t : ℝ, 0 < t → (P {ω | t < X ω}).toReal ≤ Real.exp (-t) := by
    intro t ht
    have hδ0 : 0 < Real.exp (-t) := Real.exp_pos _
    have hδ1 : Real.exp (-t) < 1 := by exact Real.exp_lt_one_iff.mpr (by linarith)
    have hmain := RegretBandits.Adversarial.exp3P_high_prob_regret_any_conf hK n hn g P I hI
      (Real.exp (-t)) hδ0 hδ1
    have hlogδ : Real.log (Real.exp (-t))⁻¹ = t := by
      rw [Real.log_inv, Real.log_exp]; ring
    rw [hlogδ] at hmain
    set E : Set Ω := {ω | regret g n I ω ≤ b * t + a} with hE
    have hEm : MeasurableSet E := measurableSet_le hRm measurable_const
    have hsub : {ω | t < X ω} ⊆ Eᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      simp only [hE, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      have hX' : X ω = (R ω - a) / b := by
        show max 0 ((R ω - a) / b) = (R ω - a) / b
        rcases le_total 0 ((R ω - a) / b) with h | h
        · exact max_eq_right h
        · have : X ω = 0 := max_eq_left h
          linarith
      have hω' : t < (R ω - a) / b := hX' ▸ hω
      rw [lt_div_iff₀ hbpos] at hω'
      show b * t + a < R ω
      linarith
    have hc : P Eᶜ ≤ ENNReal.ofReal (Real.exp (-t)) := by
      rw [prob_compl_eq_one_sub hEm]
      have : ENNReal.ofReal (1 - Real.exp (-t)) ≤ P E := hmain
      rw [ENNReal.ofReal_sub _ hδ0.le, ENNReal.ofReal_one] at this
      calc 1 - P E ≤ 1 - (1 - ENNReal.ofReal (Real.exp (-t))) := tsub_le_tsub_left this _
        _ ≤ ENNReal.ofReal (Real.exp (-t)) := by
          rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top]
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hδ1.le
    have := (measure_mono hsub).trans hc
    rw [← ENNReal.toReal_ofReal hδ0.le]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top this
  have hXlayer : ∫ ω, X ω ∂P = ∫ t in Set.Ioi (0 : ℝ), (P {ω | t < X ω}).toReal :=
    hXint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall (fun ω => le_max_left _ _))
  have hX1 : ∫ ω, X ω ∂P ≤ 1 := by
    rw [hXlayer]
    calc ∫ t in Set.Ioi (0 : ℝ), (P {ω | t < X ω}).toReal
        ≤ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
          · exact (integrableOn_exp_neg_Ioi 0)
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact htail t ht
      _ = 1 := integral_exp_neg_Ioi_zero
  calc ∫ ω, regret g n I ω ∂P = ∫ ω, R ω ∂P := rfl
    _ ≤ ∫ ω, (a + b * X ω) ∂P := integral_mono hRint
        ((integrable_const a).add (hXint.const_mul b)) hRle
    _ = a + b * ∫ ω, X ω ∂P := by
        rw [integral_add (integrable_const a) (hXint.const_mul b), integral_const,
          integral_const_mul]
        simp
    _ ≤ a + b * 1 := by gcongr
    _ = a + b := by ring
