-- Prove2me | solution 1 for RobbinsSeqDesign.StayOrSwitch.expected_average_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T13:08:08.462393+00:00
-- url     : https://prove2.me/submissions/d368f2f3-aa01-4df1-a4ef-a312eb2c3ac6

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules
import Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_head_prob_tendsto

open MeasureTheory ProbabilityTheory Filter Topology

namespace RSDcore
open RobbinsSeqDesign.StayOrSwitch BanditAlgorithm

lemma step (α β : unitInterval) (t : ℕ) (S : Set (Fin 2 × ℝ)) (hS : MeasurableSet S) :
    banditTrajMeasure (coins α β) ruleR1 {ω | ω (t+1) ∈ S} =
      ∫⁻ ω, (coins α β).P (stayOrSwitch (ω t)) {r | (stayOrSwitch (ω t), r) ∈ S}
        ∂(banditTrajMeasure (coins α β) ruleR1) := by
  set μ := banditTrajMeasure (coins α β) ruleR1 with hμ
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
  simp only [ruleR1, Kernel.deterministic_apply]
  rw [lintegral_dirac]
  rfl

end RSDcore

namespace RSDcore
open RobbinsSeqDesign.StayOrSwitch BanditAlgorithm

lemma init (α β : unitInterval) (S : Set (Fin 2 × ℝ)) (hS : MeasurableSet S) :
    banditTrajMeasure (coins α β) ruleR1 {ω | ω 0 ∈ S} =
      ∫⁻ b, (coins α β).P b {r | (b, r) ∈ S} ∂fairCoinChoice := by
  set μ := banditTrajMeasure (coins α β) ruleR1 with hμ
  have hmap : μ.map (Preorder.frestrictLe 0) =
      (banditStepKernel (coins α β) ruleR1 0 fun t ↦ t.elim0).map
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

end RSDcore

namespace RSDcore
open RobbinsSeqDesign.StayOrSwitch BanditAlgorithm

/-- the law of the coin used at trajectory coordinate `t` -/
noncomputable def nu (α β : unitInterval) : ℕ → Measure (Fin 2)
  | 0 => fairCoinChoice
  | t + 1 => (banditTrajMeasure (coins α β) ruleR1).map (fun ω ↦ stayOrSwitch (ω t))

lemma lawG (α β : unitInterval) (t : ℕ) (S : Set (Fin 2 × ℝ)) (hS : MeasurableSet S) :
    banditTrajMeasure (coins α β) ruleR1 {ω | ω t ∈ S} =
      nu α β t {0} * coinLaw α {r | ((0 : Fin 2), r) ∈ S} +
        nu α β t {1} * coinLaw β {r | ((1 : Fin 2), r) ∈ S} := by
  have key : banditTrajMeasure (coins α β) ruleR1 {ω | ω t ∈ S} =
      ∫⁻ b, (coins α β).P b {r | (b, r) ∈ S} ∂(nu α β t) := by
    cases t with
    | zero => exact init α β S hS
    | succ t =>
      have hm : Measurable (fun ω : ℕ → Fin 2 × ℝ ↦ stayOrSwitch (ω t)) :=
        measurable_stayOrSwitch.comp (measurable_pi_apply t)
      rw [step α β t S hS, nu, lintegral_map (measurable_of_countable _) hm]
  rw [key, lintegral_fintype, Fin.sum_univ_two]
  simp [coins, mul_comm]

lemma coin_one (a : unitInterval) : coinLaw a {r | r = 1} = ENNReal.ofReal a := by
  simp [coinLaw]

lemma coin_ne_one (a : unitInterval) : coinLaw a {r | ¬ r = 1} = ENNReal.ofReal (1 - a) := by
  simp [coinLaw, Set.indicator]

end RSDcore

namespace RSDcore
open RobbinsSeqDesign.StayOrSwitch BanditAlgorithm

lemma nu_sum (α β : unitInterval) (t : ℕ) : nu α β t {0} + nu α β t {1} = 1 := by
  have h := lawG α β t Set.univ MeasurableSet.univ
  simp only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one] at h
  exact h.symm

lemma nu_ne_top (α β : unitInterval) (t : ℕ) (a : Fin 2) : nu α β t {a} ≠ ⊤ := by
  have h := nu_sum α β t
  fin_cases a
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_self_add)
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_add_self)

lemma coin0_eq (α β : unitInterval) (t : ℕ) :
    banditTrajMeasure (coins α β) ruleR1 {ω | (ω t).1 = 0} = nu α β t {0} := by
  have h := lawG α β t {y | y.1 = 0} (measurableSet_eq_fun measurable_fst measurable_const)
  simpa using h

lemma head_eq (α β : unitInterval) (t : ℕ) :
    banditTrajMeasure (coins α β) ruleR1 {ω | (ω t).2 = 1} =
      nu α β t {0} * ENNReal.ofReal α + nu α β t {1} * ENNReal.ofReal β := by
  have h := lawG α β t {y | y.2 = 1} (measurableSet_eq_fun measurable_snd measurable_const)
  have e : ∀ b : Fin 2, {r : ℝ | (b, r) ∈ {y : Fin 2 × ℝ | y.2 = 1}} = {r | r = 1} :=
    fun b ↦ rfl
  rw [e, e, coin_one, coin_one] at h
  exact h

lemma nu_succ (α β : unitInterval) (t : ℕ) :
    nu α β (t + 1) {0} =
      nu α β t {0} * ENNReal.ofReal α + nu α β t {1} * ENNReal.ofReal (1 - β) := by
  have hm : Measurable (fun ω : ℕ → Fin 2 × ℝ ↦ stayOrSwitch (ω t)) :=
    measurable_stayOrSwitch.comp (measurable_pi_apply t)
  rw [nu, Measure.map_apply hm (measurableSet_singleton _)]
  have h := lawG α β t {y | stayOrSwitch y = 0}
    (measurable_stayOrSwitch (measurableSet_singleton 0))
  have e0 : {r : ℝ | ((0 : Fin 2), r) ∈ {y : Fin 2 × ℝ | stayOrSwitch y = 0}} = {r | r = 1} := by
    ext r; by_cases hr : r = 1 <;> simp [stayOrSwitch, otherCoin, hr]
  have e1 : {r : ℝ | ((1 : Fin 2), r) ∈ {y : Fin 2 × ℝ | stayOrSwitch y = 0}} = {r | ¬ r = 1} := by
    ext r; by_cases hr : r = 1 <;> simp [stayOrSwitch, otherCoin, hr]
  rw [e0, e1, coin_one, coin_ne_one] at h
  exact h

/-- real version: `u t = P(A_t = A)` -/
noncomputable def u (α β : unitInterval) (t : ℕ) : ℝ := (nu α β t {0}).toReal

lemma nu_one_real (α β : unitInterval) (t : ℕ) : (nu α β t {1}).toReal = 1 - u α β t := by
  have h := congrArg ENNReal.toReal (nu_sum α β t)
  rw [ENNReal.toReal_add (nu_ne_top _ _ _ _) (nu_ne_top _ _ _ _)] at h
  simp only [ENNReal.toReal_one] at h
  unfold u; linarith

lemma head_real (α β : unitInterval) (t : ℕ) :
    (banditTrajMeasure (coins α β) ruleR1).real {ω | (ω t).2 = 1} =
      u α β t * α + (1 - u α β t) * β := by
  rw [measureReal_def, head_eq, ENNReal.toReal_add (ENNReal.mul_ne_top (nu_ne_top _ _ _ _)
    ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top (nu_ne_top _ _ _ _) ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, nu_one_real, ENNReal.toReal_ofReal α.2.1,
    ENNReal.toReal_ofReal β.2.1]
  rfl

lemma u_succ (α β : unitInterval) (t : ℕ) :
    u α β (t + 1) = u α β t * α + (1 - u α β t) * (1 - β) := by
  have hb : (0 : ℝ) ≤ 1 - β := by linarith [β.2.2]
  rw [u, nu_succ, ENNReal.toReal_add (ENNReal.mul_ne_top (nu_ne_top _ _ _ _)
    ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top (nu_ne_top _ _ _ _) ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, nu_one_real, ENNReal.toReal_ofReal α.2.1,
    ENNReal.toReal_ofReal hb]
  rfl

lemma u_zero (α β : unitInterval) : u α β 0 = 1 / 2 := by
  simp [u, nu, fairCoinChoice]

lemma payoff_ae (α β : unitInterval) (t : ℕ) :
    (fun ω : ℕ → Fin 2 × ℝ ↦ (ω t).2) =ᵐ[banditTrajMeasure (coins α β) ruleR1]
      Set.indicator {ω | (ω t).2 = 1} 1 := by
  have hbad : banditTrajMeasure (coins α β) ruleR1 {ω | ω t ∈ {y : Fin 2 × ℝ | y.2 ≠ 0 ∧ y.2 ≠ 1}} = 0 := by
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
    ∫ ω, (ω t).2 ∂(banditTrajMeasure (coins α β) ruleR1) =
      (banditTrajMeasure (coins α β) ruleR1).real {ω | (ω t).2 = 1} := by
  rw [integral_congr_ae (payoff_ae α β t), integral_indicator_one]
  exact measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply t)) measurable_const

lemma integrable_payoff (α β : unitInterval) (t : ℕ) :
    Integrable (fun ω : ℕ → Fin 2 × ℝ ↦ (ω t).2) (banditTrajMeasure (coins α β) ruleR1) := by
  refine Integrable.congr ?_ (payoff_ae α β t).symm
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply t)) measurable_const)

lemma expectedAverage_eq (α β : unitInterval) (n : ℕ) :
    expectedAverage ruleR1 α β n = (∑ i ∈ Finset.Icc 1 n, headProb ruleR1 α β i) / n := by
  rw [expectedAverage, integral_div]
  congr 1
  unfold totalPayoff
  rw [integral_finsetSum _ (fun t _ ↦ integrable_payoff α β t)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), integral_payoff]
    rfl

end RSDcore

open RobbinsSeqDesign.StayOrSwitch in
theorem solution (α β : unitInterval)
    (hnot0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0)) (hnot1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1)) :
    Tendsto (fun n => expectedAverage ruleR1 α β n) atTop
        (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) ∧
      Tendsto (fun n => (∑ i ∈ Finset.Icc 1 n, headProb ruleR1 α β i) / n) atTop
        (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) := by
  obtain ⟨hlim, hL⟩ := head_prob_tendsto α β hnot0 hnot1
  rw [hL] at hlim
  have hsh : Tendsto (fun t : ℕ ↦ headProb ruleR1 α β (t + 1)) atTop
      (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, headProb ruleR1 α β i =
      ∑ t ∈ Finset.range n, headProb ruleR1 α β (t + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]
  have h2 : Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.Icc 1 n, headProb ruleR1 α β i) / n) atTop
      (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) := by
    refine hsh.cesaro.congr (fun n ↦ ?_)
    rw [hsum, div_eq_inv_mul]
  refine ⟨?_, h2⟩
  refine h2.congr (fun n ↦ ?_)
  rw [RSDcore.expectedAverage_eq]
