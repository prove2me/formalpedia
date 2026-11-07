-- Prove2me | solution 1 for RobbinsSeqDesign.StayOrSwitch.rule_R0_loss
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T13:10:11.724221+00:00
-- url     : https://prove2.me/submissions/82b176f7-721e-4992-8735-c93c4b508aa9

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules

open MeasureTheory ProbabilityTheory Filter Topology

namespace RSDcoreR0
open RobbinsSeqDesign.StayOrSwitch BanditAlgorithm

lemma step (α β : unitInterval) (t : ℕ) (S : Set (Fin 2 × ℝ)) (hS : MeasurableSet S) :
    banditTrajMeasure (coins α β) ruleR0 {ω | ω (t+1) ∈ S} =
      ∫⁻ ω, (coins α β).P (ω 0).1 {r | ((ω 0).1, r) ∈ S}
        ∂(banditTrajMeasure (coins α β) ruleR0) := by
  set μ := banditTrajMeasure (coins α β) ruleR0 with hμ
  have h1 : μ {ω | ω (t+1) ∈ S} =
      (μ.map (fun x ↦ (Preorder.frestrictLe t x, x (t + 1)))) (Set.univ ×ˢ S) := by
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod hS)]
    congr 1
    ext ω
    simp
  rw [h1, hμ, banditTrajMeasure,
    ← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.compProd_apply_prod MeasurableSet.univ hS, setLIntegral_univ,
    lintegral_map (Kernel.measurable_coe _ hS) (by fun_prop)]
  congr 1
  funext ω
  rw [banditTrajKernel, Kernel.comap_apply, banditStepKernel, Kernel.compProd_apply hS]
  simp only [ruleR0, Kernel.deterministic_apply]
  rw [lintegral_dirac]
  rfl

lemma init (α β : unitInterval) (S : Set (Fin 2 × ℝ)) (hS : MeasurableSet S) :
    banditTrajMeasure (coins α β) ruleR0 {ω | ω 0 ∈ S} =
      ∫⁻ b, (coins α β).P b {r | (b, r) ∈ S} ∂fairCoinChoice := by
  set μ := banditTrajMeasure (coins α β) ruleR0 with hμ
  have hmap : μ.map (Preorder.frestrictLe 0) =
      (banditStepKernel (coins α β) ruleR0 0 fun t ↦ t.elim0).map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ Fin 2 × ℝ)).symm := by
    rw [hμ, banditTrajMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have hmS : MeasurableSet {x : Π _ : Finset.Iic 0, Fin 2 × ℝ | x ⟨0, Finset.mem_Iic.mpr le_rfl⟩ ∈ S} :=
    (measurable_pi_apply (X := fun _ : Finset.Iic 0 ↦ Fin 2 × ℝ) _) hS
  have h1 : μ {ω | ω 0 ∈ S} = (μ.map (Preorder.frestrictLe 0))
      {x | x ⟨0, Finset.mem_Iic.mpr le_rfl⟩ ∈ S} := by
    rw [Measure.map_apply (by fun_prop) hmS]
    rfl
  rw [h1, hmap, Measure.map_apply (by fun_prop) hmS]
  have h2 : (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ Fin 2 × ℝ)).symm ⁻¹'
      {x | x ⟨0, Finset.mem_Iic.mpr le_rfl⟩ ∈ S} = S := by
    ext y; simp [MeasurableEquiv.piUnique, Equiv.piUnique]
  rw [h2, banditStepKernel, Kernel.compProd_apply hS]
  rfl

noncomputable def nu (α β : unitInterval) : ℕ → Measure (Fin 2)
  | 0 => fairCoinChoice
  | _ + 1 => (banditTrajMeasure (coins α β) ruleR0).map (fun ω ↦ (ω 0).1)

lemma lawG (α β : unitInterval) (t : ℕ) (S : Set (Fin 2 × ℝ)) (hS : MeasurableSet S) :
    banditTrajMeasure (coins α β) ruleR0 {ω | ω t ∈ S} =
      nu α β t {0} * coinLaw α {r | ((0 : Fin 2), r) ∈ S} +
        nu α β t {1} * coinLaw β {r | ((1 : Fin 2), r) ∈ S} := by
  have key : banditTrajMeasure (coins α β) ruleR0 {ω | ω t ∈ S} =
      ∫⁻ b, (coins α β).P b {r | (b, r) ∈ S} ∂(nu α β t) := by
    cases t with
    | zero => exact init α β S hS
    | succ t =>
      have hm : Measurable (fun ω : ℕ → Fin 2 × ℝ ↦ (ω 0).1) :=
        measurable_fst.comp (measurable_pi_apply 0)
      rw [step α β t S hS, nu, lintegral_map (measurable_of_countable _) hm]
  rw [key, lintegral_fintype, Fin.sum_univ_two]
  simp [coins, mul_comm]

lemma coin_one (a : unitInterval) : coinLaw a {r | r = 1} = ENNReal.ofReal a := by
  simp [coinLaw]

lemma fair_apply (a : Fin 2) : fairCoinChoice {a} = 1 / 2 := by
  simp [fairCoinChoice]

lemma nu_half (α β : unitInterval) (t : ℕ) (a : Fin 2) : nu α β t {a} = 1 / 2 := by
  cases t with
  | zero => exact fair_apply a
  | succ t =>
    have hm : Measurable (fun ω : ℕ → Fin 2 × ℝ ↦ (ω 0).1) :=
      measurable_fst.comp (measurable_pi_apply 0)
    rw [nu, Measure.map_apply hm (measurableSet_singleton _)]
    have h := init α β {y | y.1 = a} (measurableSet_eq_fun measurable_fst measurable_const)
    have e : (fun ω : ℕ → Fin 2 × ℝ ↦ (ω 0).1) ⁻¹' {a} = {ω | ω 0 ∈ {y : Fin 2 × ℝ | y.1 = a}} :=
      rfl
    rw [e, h, lintegral_fintype, Fin.sum_univ_two]
    fin_cases a <;> simp [coins, fair_apply]

lemma head_real (α β : unitInterval) (t : ℕ) :
    (banditTrajMeasure (coins α β) ruleR0).real {ω | (ω t).2 = 1} = ((α : ℝ) + β) / 2 := by
  have h := lawG α β t {y | y.2 = 1} (measurableSet_eq_fun measurable_snd measurable_const)
  have e : ∀ b : Fin 2, {r : ℝ | (b, r) ∈ {y : Fin 2 × ℝ | y.2 = 1}} = {r | r = 1} :=
    fun b ↦ rfl
  rw [e, e, coin_one, coin_one, nu_half, nu_half] at h
  have h' : banditTrajMeasure (coins α β) ruleR0 {ω | (ω t).2 = 1} =
      1 / 2 * ENNReal.ofReal α + 1 / 2 * ENNReal.ofReal β := h
  rw [measureReal_def, h', ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal α.2.1,
    ENNReal.toReal_ofReal β.2.1]
  simp
  ring

lemma payoff_ae (α β : unitInterval) (t : ℕ) :
    (fun ω : ℕ → Fin 2 × ℝ ↦ (ω t).2) =ᵐ[banditTrajMeasure (coins α β) ruleR0]
      Set.indicator {ω | (ω t).2 = 1} 1 := by
  have hbad : banditTrajMeasure (coins α β) ruleR0 {ω | ω t ∈ {y : Fin 2 × ℝ | y.2 ≠ 0 ∧ y.2 ≠ 1}} = 0 := by
    have hm : MeasurableSet {y : Fin 2 × ℝ | y.2 ≠ 0 ∧ y.2 ≠ 1} :=
      (measurableSet_eq_fun measurable_snd measurable_const).compl.inter
        (measurableSet_eq_fun measurable_snd measurable_const).compl
    rw [lawG α β t _ hm]
    have e : ∀ a : unitInterval, coinLaw a {r | r ≠ 0 ∧ r ≠ 1} = 0 := by
      intro a
      simp [coinLaw]
    have e2 : ∀ b : Fin 2, {r : ℝ | (b, r) ∈ {y : Fin 2 × ℝ | y.2 ≠ 0 ∧ y.2 ≠ 1}} =
        {r | r ≠ 0 ∧ r ≠ 1} := fun b ↦ rfl
    rw [e2, e2, e, e]
    simp
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null ?_ hbad
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_cases h1 : (ω t).2 = 1
  · simp [Set.indicator, h1] at hω
  · refine ⟨?_, h1⟩
    intro h0
    simp [Set.indicator, h0] at hω

lemma integral_payoff (α β : unitInterval) (t : ℕ) :
    ∫ ω, (ω t).2 ∂(banditTrajMeasure (coins α β) ruleR0) =
      (banditTrajMeasure (coins α β) ruleR0).real {ω | (ω t).2 = 1} := by
  rw [integral_congr_ae (payoff_ae α β t), integral_indicator_one]
  exact measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply t)) measurable_const

lemma integrable_payoff (α β : unitInterval) (t : ℕ) :
    Integrable (fun ω : ℕ → Fin 2 × ℝ ↦ (ω t).2) (banditTrajMeasure (coins α β) ruleR0) := by
  refine Integrable.congr ?_ (payoff_ae α β t).symm
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply t)) measurable_const)

lemma expectedAverage_eq (α β : unitInterval) (n : ℕ) (hn : 1 ≤ n) :
    expectedAverage ruleR0 α β n = ((α : ℝ) + β) / 2 := by
  rw [expectedAverage, integral_div]
  unfold totalPayoff
  rw [integral_finsetSum _ (fun t _ ↦ integrable_payoff α β t)]
  simp only [integral_payoff, head_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

end RSDcoreR0

open RobbinsSeqDesign.StayOrSwitch in
theorem solution :
    (∀ α β : unitInterval, ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0) → ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1) →
        Tendsto (fun n => max (α : ℝ) β - expectedAverage ruleR0 α β n) atTop
          (𝓝 (delta α β))) ∧
      (∀ α β : ℝ, 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 → ¬(α = 0 ∧ β = 0) → ¬(α = 1 ∧ β = 1) →
        delta α β ≤ 1 / 2) ∧
      delta 0 1 = 1 / 2 ∧ delta 1 0 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β _ _
    have hc : max (α : ℝ) β - ((α : ℝ) + β) / 2 = delta α β := by
      unfold delta
      rcases le_total (α : ℝ) β with h | h
      · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
    rw [← hc]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [RSDcoreR0.expectedAverage_eq α β n hn]
  · intro α β h0 h1 h2 h3 _ _
    unfold delta
    have : |α - β| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  · norm_num [delta]
  · norm_num [delta]
