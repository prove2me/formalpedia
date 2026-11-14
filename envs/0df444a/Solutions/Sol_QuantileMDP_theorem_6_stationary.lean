-- Prove2me | solution 1 for QuantileMDP.theorem_6_stationary
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-14T02:31:35.90336+00:00
-- url     : https://prove2.me/submissions/db01c73c-24a8-4384-b719-ead1a36e5a3b

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Definitions.Def_QuantileMDP_quantile
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_QuantileMDP_discountedPath
import Theorems.Thm_QuantileMDP_theorem_2
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QuantileMDP_trajectory
import Mathlib.Data.EReal.Inv
import Definitions.Def_QuantileMDP_discountedIteration
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Instances.EReal.Lemmas

open Filter
open scoped Topology

namespace QuantileMDP

/-- Uniform bound on the tail of a bounded discounted reward sequence.
The bound is independent of the policy and the path. -/
theorem discounted_truncation_bound (r : ℕ → ℝ) (γ R : ℝ)
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) (hR : ∀ k, |r k| ≤ R) (n : ℕ) :
    |(∑' k, γ ^ k * r k) - ∑ k ∈ Finset.range n, γ ^ k * r k| ≤
      R * γ ^ n / (1 - γ) := by
  have hg : Summable (fun k : ℕ => γ ^ k) := summable_geometric_of_lt_one hγ₀ hγ₁
  have hsum : Summable (fun k : ℕ => γ ^ k * r k) := by
    apply Summable.of_norm_bounded (hg.mul_left R)
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ₀ k), mul_comm R]
    exact mul_le_mul_of_nonneg_left (hR k) (pow_nonneg hγ₀ k)
  have hshift : Summable (fun k : ℕ => γ ^ (k + n) * r (k + n)) :=
    (summable_nat_add_iff n).2 hsum
  have habs : Summable (fun k : ℕ => ‖γ ^ (k + n) * r (k + n)‖) := by
    simpa only [Real.norm_eq_abs] using hshift.abs
  rw [← hsum.sum_add_tsum_nat_add n, add_sub_cancel_left]
  calc
    |∑' k : ℕ, γ ^ (k + n) * r (k + n)| ≤ ∑' k : ℕ, |γ ^ (k + n) * r (k + n)| :=
      by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm habs
    _ ≤ ∑' k : ℕ, (R * γ ^ n) * γ ^ k := by
      apply hshift.abs.tsum_le_tsum _ (hg.mul_left _)
      intro k
      rw [abs_mul, abs_of_nonneg (pow_nonneg hγ₀ _), pow_add]
      calc
        γ ^ k * γ ^ n * |r (k + n)| ≤ γ ^ k * γ ^ n * R :=
          mul_le_mul_of_nonneg_left (hR (k + n)) (mul_nonneg (pow_nonneg hγ₀ k) (pow_nonneg hγ₀ n))
        _ = (R * γ ^ n) * γ ^ k := by ring
    _ = R * γ ^ n / (1 - γ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hγ₀ hγ₁, div_eq_mul_inv]

end QuantileMDP

open MeasureTheory Set QuantileMDP
open scoped ENNReal

namespace QuantileMDP

/-- An almost-sure additive bound on real rewards gives the same bound on
their extended-real quantiles, at both endpoints as well. -/
theorem quantile_le_add_of_ae_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (c τ : ℝ)
    (hXY : ∀ᵐ ω ∂P, X ω ≤ Y ω + c) :
    quantile (P.map X) τ ≤ quantile (P.map Y) τ + (c : EReal) := by
  let e : EReal ≃o EReal :=
    { toFun := fun x => x + (c : EReal)
      invFun := fun x => x - (c : EReal)
      left_inv := fun _ => EReal.add_sub_cancel_right
      right_inv := fun _ => EReal.sub_add_cancel
      map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right }
  have hclosed (x : ℝ) : (P.map Y) (Iic x) ≤ (P.map X) (Iic (x + c)) := by
    rw [Measure.map_apply hX measurableSet_Iic, Measure.map_apply hY measurableSet_Iic]
    refine measure_mono_ae ?_
    filter_upwards [hXY] with ω hω hx
    exact mem_Iic.mpr (hω.trans (add_le_add_left hx c))
  have hupper (x : ℝ) : (P.map X) (Ici x) ≤ (P.map Y) (Ici (x - c)) := by
    rw [Measure.map_apply hX measurableSet_Ici, Measure.map_apply hY measurableSet_Ici]
    refine measure_mono_ae ?_
    filter_upwards [hXY] with ω hω hx
    exact mem_Ici.mpr (sub_le_iff_le_add.mpr (hx.trans hω))
  have he (x : ℝ) : e (x : EReal) = ((x + c : ℝ) : EReal) :=
    (EReal.coe_add _ _).symm
  change _ ≤ e (quantile (P.map Y) τ)
  simp only [quantile]
  split_ifs with h0 h1
  · rw [e.map_sSup]
    apply sSup_le
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : (P.map X) (Ici x) = 1 := hx
    let := Measure.isProbabilityMeasure_map (μ := P) hY.aemeasurable
    have hy1 : (P.map Y) (Ici (x - c)) = 1 :=
      le_antisymm prob_le_one (hx1 ▸ hupper x)
    have hx' : (x : EReal) = e ((x - c : ℝ) : EReal) := by rw [he, sub_add_cancel]
    change (x : EReal) ≤ _
    rw [hx']
    apply le_iSup_of_le ((x - c : ℝ) : EReal)
    exact le_iSup_of_le ⟨x - c, hy1, rfl⟩ le_rfl
  · rw [e.map_sInf]
    refine le_iInf fun y => le_iInf fun hy => ?_
    obtain ⟨y, hy, rfl⟩ := hy
    rw [he]
    let := Measure.isProbabilityMeasure_map (μ := P) hX.aemeasurable
    have hx1 : (P.map X) (Iic (y + c)) = 1 :=
      le_antisymm prob_le_one ((show (P.map Y) (Iic y) = 1 from hy) ▸ hclosed y)
    exact sInf_le ⟨y + c, hx1, rfl⟩
  · rw [e.map_sInf]
    refine le_iInf fun y => le_iInf fun hy => ?_
    obtain ⟨y, hy, rfl⟩ := hy
    rw [he]
    exact sInf_le ⟨y + c,
      (show ENNReal.ofReal τ ≤ (P.map Y) (Iic y) from hy).trans (hclosed y), rfl⟩

end QuantileMDP

open QuantileMDP MeasureTheory Filter
open scoped Topology

namespace QuantileMDP

/-- Uniform comparison of optimal truncated and infinite discounted quantiles.
The reward processes can have different path laws for different policies.
The bound is uniform in the initial state and the quantile level. -/
theorem discounted_value_truncation {S Policies Ω : Type*} [MeasurableSpace Ω]
    (P : S → Policies → Measure Ω) (hP : ∀ s π, IsProbabilityMeasure (P s π))
    (reward : S → Policies → ℕ → Ω → ℝ) (γ R : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hR : ∀ s π k, ∀ ω, |reward s π k ω| ≤ R)
    (hpartial : ∀ s π n, Measurable (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward s π k ω))
    (hfull : ∀ s π, Measurable (fun ω => ∑' k, γ ^ k * reward s π k ω))
    (s : S) (n : ℕ) (τ : ℝ) :
    let Vₙ := ⨆ π, quantile ((P s π).map (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward s π k ω)) τ
    let V := ⨆ π, quantile ((P s π).map (fun ω => ∑' k, γ ^ k * reward s π k ω)) τ
    let ε := R * γ ^ n / (1 - γ)
    Vₙ ≤ V + (ε : EReal) ∧ V ≤ Vₙ + (ε : EReal) := by
  dsimp only
  let ε := R * γ ^ n / (1 - γ)
  let partialSum (π : Policies) (ω : Ω) := ∑ k ∈ Finset.range n, γ ^ k * reward s π k ω
  let totalSum (π : Policies) (ω : Ω) := ∑' k, γ ^ k * reward s π k ω
  let e : EReal ≃o EReal :=
    { toFun := fun x => x + (ε : EReal)
      invFun := fun x => x - (ε : EReal)
      left_inv := fun _ => EReal.add_sub_cancel_right
      right_inv := fun _ => EReal.sub_add_cancel
      map_rel_iff' := (EReal.addLECancellable_coe ε).add_le_add_iff_right }
  change
    (⨆ π, quantile ((P s π).map (partialSum π)) τ) ≤
      e (⨆ π, quantile ((P s π).map (totalSum π)) τ) ∧
    (⨆ π, quantile ((P s π).map (totalSum π)) τ) ≤
      e (⨆ π, quantile ((P s π).map (partialSum π)) τ)
  simp only [e.map_iSup]
  have hpoint (π : Policies) (ω : Ω) : |totalSum π ω - partialSum π ω| ≤ ε :=
    discounted_truncation_bound (fun k => reward s π k ω) γ R hγ₀ hγ₁
      (fun k => hR s π k ω) n
  constructor
  · apply iSup_mono
    intro π
    let := hP s π
    exact quantile_le_add_of_ae_le (P s π) (partialSum π) (totalSum π)
      (hpartial s π n) (hfull s π) ε τ
      (ae_of_all _ fun ω => by linarith only [(abs_le.mp (hpoint π ω)).1])
  · apply iSup_mono
    intro π
    let := hP s π
    exact quantile_le_add_of_ae_le (P s π) (totalSum π) (partialSum π)
      (hfull s π) (hpartial s π n) ε τ
      (ae_of_all _ fun ω => by linarith only [(abs_le.mp (hpoint π ω)).2])

theorem discounted_truncation_error_tendsto_zero (γ R : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) :
    Tendsto (fun n : ℕ => R * γ ^ n / (1 - γ)) atTop (𝓝 0) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ₀ hγ₁).const_mul R).div_const (1 - γ)
  simpa using h


/-- The geometric error yields convergence of the policy suprema, including
when the family of policies is empty. -/
theorem discounted_value_tendsto {S Policies Ω : Type*} [MeasurableSpace Ω]
    (P : S → Policies → Measure Ω) (hP : ∀ s π, IsProbabilityMeasure (P s π))
    (reward : S → Policies → ℕ → Ω → ℝ) (γ R : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hR : ∀ s π k, ∀ ω, |reward s π k ω| ≤ R)
    (hpartial : ∀ s π n, Measurable (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward s π k ω))
    (hfull : ∀ s π, Measurable (fun ω => ∑' k, γ ^ k * reward s π k ω))
    (s : S) (τ : ℝ) :
    Tendsto (fun n : ℕ =>
      ⨆ π, quantile ((P s π).map (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward s π k ω)) τ)
      atTop (𝓝 (⨆ π, quantile ((P s π).map (fun ω => ∑' k, γ ^ k * reward s π k ω)) τ)) := by
  let Vₙ (n : ℕ) := ⨆ π, quantile
    ((P s π).map (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward s π k ω)) τ
  let V := ⨆ π, quantile ((P s π).map (fun ω => ∑' k, γ ^ k * reward s π k ω)) τ
  let ε (n : ℕ) := R * γ ^ n / (1 - γ)
  have he : Tendsto ε atTop (𝓝 0) := discounted_truncation_error_tendsto_zero γ R hγ₀ hγ₁
  have hadd (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) :
      Tendsto (fun n => V + (f n : EReal)) atTop (𝓝 V) := by
    have hc : Tendsto (fun n => (f n : EReal)) atTop (𝓝 ((0 : ℝ) : EReal)) :=
      EReal.tendsto_coe.mpr hf
    have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (V, ((0 : ℝ) : EReal)) :=
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot 0)) (Or.inr (EReal.coe_ne_top 0))
    simpa only [Function.comp_def, EReal.coe_zero, add_zero] using
      hcont.tendsto.comp ((tendsto_const_nhds (x := V)).prodMk_nhds hc)
  have hbounds (n : ℕ) : Vₙ n ≤ V + (ε n : EReal) ∧ V ≤ Vₙ n + (ε n : EReal) :=
    discounted_value_truncation P hP reward γ R hγ₀ hγ₁ hR hpartial hfull s n τ
  change Tendsto Vₙ atTop (𝓝 V)
  refine tendsto_order.mpr ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hen : Tendsto (fun n => -ε n) atTop (𝓝 0) := by simpa only [neg_zero] using he.neg
    filter_upwards [(hadd _ hen).eventually_const_lt hb] with n hn
    have hlo : V - (ε n : EReal) ≤ Vₙ n := by
      apply (EReal.addLECancellable_coe (ε n)).add_le_add_iff_right.mp
      rw [EReal.sub_add_cancel]
      exact (hbounds n).2
    exact (by simpa only [sub_eq_add_neg, EReal.coe_neg] using hn : b < V - (ε n : EReal)).trans_le hlo
  · filter_upwards [(hadd _ he).eventually_lt_const hb] with n hn
    exact (hbounds n).1.trans_lt hn

end QuantileMDP

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace QuantileMDP

private theorem partial_reward_eq {S A : Type*} (M : Model S A) (π : Policy S A)
    (γ : ℝ) (n : ℕ) (w : ℕ → S) :
    (∑ k ∈ Finset.range n, γ ^ k * stepReward M π k w) =
      pathReward (discountedModel M γ) π (infinitePrefix w n) := by
  rw [pathReward, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rfl

theorem path_map_partial_reward {S A : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A) (π : Policy S A) (s : S)
    (P : Measure (ℕ → S)) (hP : IsPolicyPathLaw M π s P) (γ : ℝ) (n : ℕ) :
    P.map (fun w => ∑ k ∈ Finset.range n, γ ^ k * stepReward M π k w) =
      rewardLaw (discountedModel M γ) n π s := by
  classical
  let H := Fin (n + 1) → S
  have hpre : Measurable (fun w : ℕ → S => infinitePrefix w n) := by
    exact measurable_pi_lambda _ fun _ => measurable_pi_apply _
  let f : H → ℝ := fun g => pathReward (discountedModel M γ) π g
  have hf : Measurable f := measurable_of_countable f
  simp_rw [partial_reward_eq]
  change P.map (f ∘ (fun w => infinitePrefix w n)) = _
  rw [← Measure.map_map hf hpre]
  have hmap : P.map (fun w => infinitePrefix w n) =
      ∑ g : Fin n → S, pathWeight M π (Fin.cons s g) • Measure.dirac (Fin.cons s g) := by
    apply Measure.ext_of_singleton
    intro g
    rw [Measure.map_apply hpre (measurableSet_singleton _), Measure.finsetSum_apply]
    change P {w | infinitePrefix w n = g} = _
    rw [hP.2]
    by_cases hg : g 0 = s
    · have he : Fin.cons s (Fin.tail g) = g := by rw [← hg, Fin.cons_self_tail]
      rw [if_pos hg, Finset.sum_eq_single (Fin.tail g)]
      · rw [he, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_singleton _), mul_one]
      · intro j _ hj
        have hnot : Fin.cons s j ∉ ({g} : Set H) := fun h => hj (by
          simpa only [mem_singleton_iff, Fin.tail_cons] using congrArg Fin.tail (mem_singleton_iff.mp h))
        rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, indicator_of_notMem hnot, mul_zero]
      · simp
    · rw [if_neg hg]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      have hnot : Fin.cons s i ∉ ({g} : Set H) := fun h => hg (by
        simpa only [Fin.cons_zero] using (congrFun (mem_singleton_iff.mp h) 0).symm)
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, indicator_of_notMem hnot, mul_zero]
  rw [hmap, Measure.map_finset_sum' hf.aemeasurable]
  unfold rewardLaw
  apply Finset.sum_congr rfl
  intro g _
  rw [Measure.map_smul, Measure.map_dirac' hf]
  rfl

theorem measurable_stepReward {S A : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A) (π : Policy S A) (k : ℕ) :
    Measurable (stepReward M π k) := by
  let f : (Fin (k + 2) → S) → ℝ := fun h =>
    M.r k (h (Fin.last k).castSucc) (π k (Fin.init h)) (h (Fin.last (k + 1)))
  have hf : Measurable f := measurable_of_countable f
  exact hf.comp (show Measurable (fun w : ℕ → S => infinitePrefix w (k + 1)) from
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val)

/-- The finite-horizon discounted backward values converge to the infinite
policy supremum for a family of path laws realizing the prescribed kernels. -/
theorem discounted_mdp_value_limit {S A : Type*} [Fintype S] [Fintype A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S A)
    (P : S → {π : Policy S A // M.Admissible π} → Measure (ℕ → S))
    (hP : ∀ s π, IsPolicyPathLaw M π.val s (P s π))
    (γ R : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hR : ∀ k s a i, |M.r k s a i| ≤ R)
    (s : S) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    let V := ⨆ π, quantile ((P s π).map (fun w => ∑' k, γ ^ k * stepReward M π.val k w)) τ
    Tendsto (fun n => dpValue (discountedModel M γ) n 0 s τ) atTop (𝓝 V) ∧
      ∀ n, dpValue (discountedModel M γ) n 0 s τ ≤ V + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) ∧
        V ≤ dpValue (discountedModel M γ) n 0 s τ + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) := by
  let reward := fun (_ : S) (π : {π : Policy S A // M.Admissible π}) k => stepReward M π.val k
  have hpartial (s : S) (π : {π : Policy S A // M.Admissible π}) (n : ℕ) :
      Measurable (fun w => ∑ k ∈ Finset.range n, γ ^ k * reward s π k w) :=
    Finset.measurable_fun_sum _ (fun k _ => (measurable_stepReward M π.val k).const_mul _)
  have hfull (s : S) (π : {π : Policy S A // M.Admissible π}) :
      Measurable (fun w => ∑' k, γ ^ k * reward s π k w) :=
    Measurable.tsum fun k => (measurable_stepReward M π.val k).const_mul _
  have hval (n : ℕ) :
      (⨆ π, quantile ((P s π).map (fun w => ∑ k ∈ Finset.range n, γ ^ k * reward s π k w)) τ) =
        dpValue (discountedModel M γ) n 0 s τ := by
    let D := discountedModel M γ
    have h := theorem_2 D n s τ hτ
    have hadm (π : Policy S A) : D.Admissible π ↔ M.Admissible π := Iff.rfl
    apply le_antisymm
    · refine iSup_le fun π => h.2 ?_
      exact ⟨π.val, (hadm π.val).mpr π.property,
        congrArg (fun μ => quantile μ τ) (path_map_partial_reward M π.val s (P s π) (hP s π) γ n)⟩
    · obtain ⟨π, hπ, hv⟩ := h.1
      let ρ : {π : Policy S A // M.Admissible π} := ⟨π, (hadm π).mp hπ⟩
      rw [hv, ← path_map_partial_reward M π s (P s ρ) (hP s ρ) γ n]
      exact le_iSup_of_le ρ le_rfl
  have hbound (x : S) (π : {π : Policy S A // M.Admissible π}) (k : ℕ) (w : ℕ → S) :
      |reward x π k w| ≤ R := hR k _ _ _
  have hp (x : S) (π : {π : Policy S A // M.Admissible π}) := (hP x π).1
  refine ⟨?_, fun n => ?_⟩
  · have h := discounted_value_tendsto P hp reward γ R hγ₀ hγ₁ hbound hpartial hfull s τ
    simpa only [hval] using h
  · have h := discounted_value_truncation P hp reward γ R hγ₀ hγ₁ hbound hpartial hfull s n τ
    simpa only [hval] using h

end QuantileMDP

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace QuantileMDP

private theorem pathWeight_succ {S A : Type*} (M : Model S A) (π : Policy S A) (n : ℕ)
    (g : Fin (n + 2) → S) :
    pathWeight M π g = pathWeight M π (Fin.init g) *
      M.P n ((Fin.init g) (Fin.last n)) (π n (Fin.init g)) (g (Fin.last (n + 1))) := by
  rw [pathWeight, Fin.prod_univ_castSucc, pathWeight]
  congr 1

set_option maxHeartbeats 2000000 in
private theorem partialTraj_singleton {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A) (π : Policy S A) (s : S)
    (n : ℕ) (g : Finset.Iic n → S) :
    Kernel.partialTraj (X := fun _ => S) (policyKernel M π) 0 n (fun _ => s) {g} =
      if (historyEquiv S n g) 0 = s then pathWeight M π (historyEquiv S n g) else 0 := by
  classical
  induction n with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_apply, Measure.dirac_apply]
    have he : (fun _ : Finset.Iic (0 : ℕ) => s) = g ↔ (historyEquiv S 0 g) 0 = s := by
      constructor
      · intro h
        rw [← h]
        rfl
      · intro h
        funext i
        have hi : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property))
        subst i
        exact h.symm
    simp [Set.indicator, he, pathWeight]
  | succ n ih =>
    let g₀ : Finset.Iic n → S := fun j => g ⟨j.val, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp j.property).trans n.le_succ)⟩
    let z : S := g ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
    let κ := policyKernel M π
    let e := MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => S) n.le_succ
    let e' := MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) n
    have hz : e.symm g = (g₀, e' z) := by
      apply Prod.ext
      · rfl
      · funext i
        have hi : (i : ℕ) = n + 1 := Nat.mem_Ioc_succ.1 i.property
        have heq : i = ⟨n + 1, Finset.right_mem_Ioc.2 n.lt_succ_self⟩ := Subtype.ext hi
        subst i
        rfl
    have hmap : e ⁻¹' ({g} : Set (Finset.Iic (n + 1) → S)) = {e.symm g} := by
      ext x
      exact e.toEquiv.eq_symm_apply.symm
    have hexpand : ∀ h : Finset.Iic n → S,
        (Kernel.id ×ₖ (κ n).map e') h {e.symm g} =
          ({g₀} : Set (Finset.Iic n → S)).indicator (fun _ => κ n g₀ {z}) h := by
      intro h
      rw [Kernel.id_prod_apply' _ _ (measurableSet_singleton _), hz]
      by_cases heq : h = g₀
      · subst h
        have hp : Prod.mk g₀ ⁻¹' ({(g₀, e' z)} : Set ((Finset.Iic n → S) × (Finset.Ioc n (n + 1) → S))) = {e' z} := by
          ext x
          simp
        rw [hp, Set.indicator_of_mem (Set.mem_singleton _), Kernel.map_apply _ e'.measurable,
          Measure.map_apply e'.measurable (measurableSet_singleton _)]
        congr 1
        ext x
        simp
      · have hp : Prod.mk h ⁻¹' ({(g₀, e' z)} : Set ((Finset.Iic n → S) × (Finset.Ioc n (n + 1) → S))) = ∅ := by
          ext x
          simp [heq]
        rw [hp, measure_empty, Set.indicator_of_notMem (fun hh => heq (Set.mem_singleton_iff.mp hh))]
    have hs : (historyEquiv S n g₀) = Fin.init (historyEquiv S (n + 1) g) := rfl
    change Kernel.partialTraj (X := fun _ => S) κ 0 (n + 1) (fun _ => s) {g} = _
    have he : (e : ((Finset.Iic n → S) × (Finset.Ioc n (n + 1) → S)) → (Finset.Iic (n + 1) → S)) =
        _root_.IicProdIoc (X := fun _ : ℕ => S) n (n + 1) :=
      MeasurableEquiv.coe_IicProdIoc (X := fun _ : ℕ => S) n.le_succ
    rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n), ← he]
    rw [Kernel.map_apply _ e.measurable,
      Measure.map_apply e.measurable (measurableSet_singleton _), hmap,
      Kernel.comp_apply' _ _ _ (measurableSet_singleton _)]
    have hi : ∀ h : Finset.Iic n → S,
        ((Kernel.id ×ₖ (κ n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) n)) h)
          {e.symm g} = ({g₀} : Set (Finset.Iic n → S)).indicator (fun _ => κ n g₀ {z}) h :=
      hexpand
    simp_rw [hi]
    rw [lintegral_indicator_const (measurableSet_singleton _), ih]
    have hp : κ n g₀ {z} = M.P n ((historyEquiv S n g₀) (Fin.last n))
        (π n (historyEquiv S n g₀)) z := by
      exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
    rw [hp]
    have hf : (historyEquiv S n g₀) 0 = (historyEquiv S (n + 1) g) 0 := rfl
    have hl : z = (historyEquiv S (n + 1) g) (Fin.last (n + 1)) := rfl
    rw [hf, hs, hl, pathWeight_succ M π n]
    split_ifs <;> simp [mul_comm]

/-- The canonical infinite trajectory measure realizes the finite path
weights and is a probability measure. -/
theorem trajectoryLaw_isPolicyPathLaw {S A : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A) (π : Policy S A) (s : S) :
    IsPolicyPathLaw M π s (trajectoryLaw M π s) := by
  classical
  constructor
  · unfold trajectoryLaw
    infer_instance
  · intro n g
    let h := (historyEquiv S n).symm g
    have hh : {w : ℕ → S | infinitePrefix w n = g} =
        (frestrictLe n) ⁻¹' ({h} : Set (Finset.Iic n → S)) := by
      ext w
      change (infinitePrefix w n = g) ↔ _
      rw [Set.mem_preimage, Set.mem_singleton_iff, (historyEquiv S n).eq_symm_apply]
      rfl
    rw [hh, ← Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _),
      trajectoryLaw, Kernel.traj_map_frestrictLe_apply, partialTraj_singleton]
    have he : historyEquiv S n h = g := Equiv.apply_symm_apply _ _
    rw [he]

end QuantileMDP

open Set

namespace QuantileMDP

private noncomputable def scaleIso (c : ℝ) (hc : 0 < c) : EReal ≃o EReal where
  toFun x := (c : EReal) * x
  invFun x := (c⁻¹ : ℝ) * x
  left_inv x := by
    cases x <;> simp [EReal.coe_mul_bot_of_pos, EReal.coe_mul_top_of_pos, hc, inv_pos.mpr hc,
      ← EReal.coe_mul, inv_mul_cancel_left₀ hc.ne']
  right_inv x := by
    cases x <;> simp [EReal.coe_mul_bot_of_pos, EReal.coe_mul_top_of_pos, hc, inv_pos.mpr hc,
      ← EReal.coe_mul, mul_inv_cancel_left₀ hc.ne']
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;> simp [EReal.coe_mul_bot_of_pos, EReal.coe_mul_top_of_pos,
      hc, ← EReal.coe_mul, EReal.coe_le_coe_iff, mul_le_mul_iff_right₀ hc]

/-- For stationary kernels and rewards, stationary iteration is the same
as the backward recursion on geometrically discounted finite rewards. -/
theorem discountedIter_eq_dpValue {S A : Type*} [Fintype S] (M : Model S A)
    (hP : ∀ k, M.P k = M.P 0) (hr : ∀ k, M.r k = M.r 0) (ha : ∀ k, M.adm k = M.adm 0)
    (γ : ℝ) (hγ : 0 < γ) (n : ℕ) (s : S) (τ : ℝ) :
    discountedIter M γ n s τ = dpValue (discountedModel M γ) n 0 s τ := by
  have hscaled (n t : ℕ) (s : S) (τ : ℝ) :
      dpAux (discountedModel M γ) n t s τ =
        ((γ ^ t : ℝ) : EReal) * discountedIter M γ n s τ := by
    induction n generalizing t s τ with
    | zero => simp [dpAux, discountedIter]
    | succ n ih =>
      let c := γ ^ t
      let e := scaleIso c (pow_pos hγ t)
      change _ = e (discountedIter M γ (n + 1) s τ)
      rw [dpAux, discountedIter, stationaryBellman]
      simp only [e.map_iSup, discountedModel, hP, ha]
      apply congrArg iSup
      funext a
      apply congrArg iSup
      funext hadm
      unfold opt
      simp only [e.map_iSup, e.map_iInf]
      apply congrArg iSup
      funext q
      apply congrArg iSup
      funext hf
      apply congrArg iInf
      funext i
      apply congrArg iInf
      funext hi
      change dpAux (discountedModel M γ) n (t + 1) i (q i) +
        ((γ ^ t * M.r t s a i : ℝ) : EReal) = e _
      rw [ih (t + 1)]
      rw [hr t]
      change _ = ((γ ^ t : ℝ) : EReal) *
        ((γ : EReal) * discountedIter M γ n i (q i) + (M.r 0 s a i : EReal))
      rw [pow_succ, EReal.coe_mul, mul_assoc, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr
        (pow_nonneg hγ.le t)) (EReal.coe_ne_top _) _ _, ← EReal.coe_mul]
  simpa [dpValue] using (hscaled n 0 s τ).symm

end QuantileMDP

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace QuantileMDP

/-- The infinite-horizon supremum is attained if each finite truncation
depends continuously on the policy in a compact policy space. -/
theorem infinite_optimal_of_compact {Policies Ω : Type*}
    [TopologicalSpace Policies] [CompactSpace Policies] [Nonempty Policies] [MeasurableSpace Ω]
    (P : Policies → Measure Ω) (hP : ∀ π, IsProbabilityMeasure (P π))
    (reward : Policies → ℕ → Ω → ℝ) (γ R : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hR : ∀ π k ω, |reward π k ω| ≤ R) (τ : ℝ)
    (hpartial : ∀ π n, Measurable (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward π k ω))
    (hfull : ∀ π, Measurable (fun ω => ∑' k, γ ^ k * reward π k ω))
    (hfin : ∀ n, Continuous (fun π =>
      (quantile ((P π).map (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward π k ω)) τ).toReal))
    (hreal : ∀ π n, ∃ x : ℝ,
      quantile ((P π).map (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward π k ω)) τ = (x : EReal))
    (hreal' : ∀ π, ∃ x : ℝ, quantile ((P π).map (fun ω => ∑' k, γ ^ k * reward π k ω)) τ = (x : EReal)) :
    ∃ π, quantile ((P π).map (fun ω => ∑' k, γ ^ k * reward π k ω)) τ =
      ⨆ ρ, quantile ((P ρ).map (fun ω => ∑' k, γ ^ k * reward ρ k ω)) τ := by
  let V (π : Policies) := quantile ((P π).map (fun ω => ∑' k, γ ^ k * reward π k ω)) τ
  let Vₙ (n : ℕ) (π : Policies) := quantile
    ((P π).map (fun ω => ∑ k ∈ Finset.range n, γ ^ k * reward π k ω)) τ
  have hb (n : ℕ) (π : Policies) : |(V π).toReal - (Vₙ n π).toReal| ≤ R * γ ^ n / (1 - γ) := by
    let X (ω : Ω) := ∑' k, γ ^ k * reward π k ω
    let Y (ω : Ω) := ∑ k ∈ Finset.range n, γ ^ k * reward π k ω
    let δ := R * γ ^ n / (1 - γ)
    have hbound (ω : Ω) : |X ω - Y ω| ≤ δ :=
      discounted_truncation_bound (fun k => reward π k ω) γ R hγ₀ hγ₁ (fun k => hR π k ω) n
    let := hP π
    have hXY : V π ≤ Vₙ n π + (δ : EReal) :=
      quantile_le_add_of_ae_le (P π) X Y (hfull π) (hpartial π n) δ τ
        (ae_of_all _ fun ω => by linarith only [(abs_le.mp (hbound ω)).2])
    have hYX : Vₙ n π ≤ V π + (δ : EReal) :=
      quantile_le_add_of_ae_le (P π) Y X (hpartial π n) (hfull π) δ τ
        (ae_of_all _ fun ω => by linarith only [(abs_le.mp (hbound ω)).1])
    obtain ⟨a, ha⟩ : ∃ x : ℝ, V π = (x : EReal) := hreal' π
    obtain ⟨b, hb⟩ : ∃ x : ℝ, Vₙ n π = (x : EReal) := hreal π n
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hXY hYX
    rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe]
    exact abs_le.mpr ⟨by linarith only [hYX], by linarith only [hXY]⟩
  have hε : Tendsto (fun n : ℕ => R * γ ^ n / (1 - γ)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ₀ hγ₁).const_mul R).div_const (1 - γ)
  have hu : TendstoUniformly (fun n π => (Vₙ n π).toReal) (fun π => (V π).toReal) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hεpos
    filter_upwards [hε.eventually_lt_const hεpos] with n hn π
    rw [Real.dist_eq]
    exact (hb n π).trans_lt hn
  have hc := hu.continuous (Eventually.of_forall hfin).frequently
  obtain ⟨π, _, hπ⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  refine ⟨π, le_antisymm (le_iSup V π) (iSup_le fun ρ => ?_)⟩
  obtain ⟨a, ha⟩ : ∃ x : ℝ, V π = (x : EReal) := hreal' π
  obtain ⟨b, hb⟩ : ∃ x : ℝ, V ρ = (x : EReal) := hreal' ρ
  have h := hπ (Set.mem_univ ρ)
  change (V ρ).toReal ≤ (V π).toReal at h
  rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe] at h
  change V ρ ≤ V π
  rw [ha, hb, EReal.coe_le_coe_iff]
  exact h


private theorem quantile_map_real_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (B τ : ℝ) (hB : ∀ ω, |X ω| ≤ B) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ∃ x : ℝ, quantile (P.map X) τ = (x : EReal) := by
  have hconstant (c : ℝ) : quantile (P.map (fun _ : Ω => c)) τ = (c : EReal) := by
    have hm : P.map (fun _ : Ω => c) = Measure.dirac c := by simp
    rw [hm, quantile]
    split_ifs with h0 h1
    · apply le_antisymm
      · refine sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        apply EReal.coe_le_coe_iff.mpr
        by_contra! h
        have hzero : Measure.dirac c (Ici x) = 0 :=
          Measure.dirac_apply' _ measurableSet_Ici |>.trans
            (indicator_of_notMem (show c ∉ Ici x from h.not_ge) _)
        exact zero_ne_one (hzero.symm.trans hx)
      · exact le_sSup ⟨c, Measure.dirac_apply_of_mem (mem_Ici.mpr le_rfl), rfl⟩
    · apply le_antisymm
      · exact sInf_le ⟨c, Measure.dirac_apply_of_mem (mem_Iic.mpr le_rfl), rfl⟩
      · refine le_sInf ?_
        rintro _ ⟨x, hx, rfl⟩
        apply EReal.coe_le_coe_iff.mpr
        by_contra! h
        have hzero : Measure.dirac c (Iic x) = 0 :=
          Measure.dirac_apply' _ measurableSet_Iic |>.trans
            (indicator_of_notMem (show c ∉ Iic x from h.not_ge) _)
        exact zero_ne_one (hzero.symm.trans hx)
    · apply le_antisymm
      · refine sInf_le ⟨c, ?_, rfl⟩
        change ENNReal.ofReal τ ≤ Measure.dirac c (Iic c)
        rw [Measure.dirac_apply_of_mem (mem_Iic.mpr le_rfl)]
        exact ENNReal.ofReal_le_one.mpr hτ.2
      · refine le_sInf ?_
        rintro _ ⟨x, hx, rfl⟩
        apply EReal.coe_le_coe_iff.mpr
        by_contra! h
        have hzero : Measure.dirac c (Iic x) = 0 :=
          Measure.dirac_apply' _ measurableSet_Iic |>.trans
            (indicator_of_notMem (show c ∉ Iic x from h.not_ge) _)
        have hl : ENNReal.ofReal τ ≤ Measure.dirac c (Iic x) := hx
        rw [hzero] at hl
        exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hτ.1 (Ne.symm h0))).not_ge hl
  have hu := quantile_le_add_of_ae_le P X (fun _ => B) hX measurable_const 0 τ
    (ae_of_all _ fun ω => by simpa using (abs_le.mp (hB ω)).2)
  have hl := quantile_le_add_of_ae_le P (fun _ => -B) X measurable_const hX 0 τ
    (ae_of_all _ fun ω => by simpa using (abs_le.mp (hB ω)).1)
  rw [hconstant B, EReal.coe_zero, add_zero] at hu
  rw [hconstant (-B), EReal.coe_zero, add_zero] at hl
  exact ⟨_, (EReal.coe_toReal (ne_of_lt (hu.trans_lt (EReal.coe_lt_top B)))
    (ne_of_gt ((EReal.bot_lt_coe (-B)).trans_le hl))).symm⟩

end QuantileMDP

namespace QuantileMDP

private theorem prefix_policy_rewardLaw {S A : Type*} [Fintype S] (M : Model S A)
    (n : ℕ) (π ρ : Policy S A) (s : S) (h : ∀ k < n, π k = ρ k) :
    rewardLaw M n π s = rewardLaw M n ρ s := by
  unfold rewardLaw
  apply Finset.sum_congr rfl
  intro g _
  have hw : pathWeight M π (Fin.cons s g) = pathWeight M ρ (Fin.cons s g) := by
    unfold pathWeight
    exact Finset.prod_congr rfl fun i _ => by rw [h i i.isLt]
  have hr : pathReward M π (Fin.cons s g) = pathReward M ρ (Fin.cons s g) := by
    unfold pathReward
    exact Finset.sum_congr rfl fun i _ => by rw [h i i.isLt]
  rw [hw, hr]

/-- In a finite-state, finite-action discounted model the infinite policy
supremum is attained for every starting state and quantile level. -/
theorem infinite_optimal_exists {S A : Type*} [Fintype S] [Fintype A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S A) (s : S)
    (P : {π : Policy S A // M.Admissible π} → Measure (ℕ → S))
    (hP : ∀ π, IsPolicyPathLaw M π.val s (P π))
    (γ R : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) (hR : ∀ k s a i, |M.r k s a i| ≤ R)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ∃ π : {π : Policy S A // M.Admissible π},
      quantile ((P π).map (fun w => ∑' k, γ ^ k * stepReward M π.val k w)) τ =
        ⨆ ρ, quantile ((P ρ).map (fun w => ∑' k, γ ^ k * stepReward M ρ.val k w)) τ := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let Good := {π : Policy S A // M.Admissible π}
  let : TopologicalSpace (Policy S A) :=
    inferInstanceAs (TopologicalSpace ((k : ℕ) → (Fin (k + 1) → S) → A))
  have hset : IsClosed {π : Policy S A | M.Admissible π} := by
    have he : {π : Policy S A | M.Admissible π} =
        ⋂ (k : ℕ) (h : Fin (k + 1) → S), (fun π : Policy S A => π k h) ⁻¹'
          M.adm k (h (Fin.last k)) := by
      ext π
      simp [Model.Admissible]
    rw [he]
    exact isClosed_iInter fun k => isClosed_iInter fun h =>
      (isClosed_discrete _).preimage ((continuous_apply h).comp (continuous_apply k))
  let : CompactSpace (Policy S A) := inferInstanceAs
    (CompactSpace ((k : ℕ) → (Fin (k + 1) → S) → A))
  let : CompactSpace Good := isCompact_iff_compactSpace.mp hset.isCompact
  let d : Policy S A := fun k h => (M.adm_nonempty k (h (Fin.last k))).choose
  let : Nonempty Good := ⟨⟨d, fun k h => (M.adm_nonempty k (h (Fin.last k))).choose_spec⟩⟩
  let reward : Good → ℕ → (ℕ → S) → ℝ := fun π k => stepReward M π.val k
  have hp (π : Good) := (hP π).1
  have hpartial (π : Good) (n : ℕ) :
      Measurable (fun w => ∑ k ∈ Finset.range n, γ ^ k * reward π k w) :=
    Finset.measurable_fun_sum _ fun k _ => (measurable_stepReward M π.val k).const_mul _
  have hfull (π : Good) :
      Measurable (fun w => ∑' k, γ ^ k * reward π k w) :=
    Measurable.tsum fun k => (measurable_stepReward M π.val k).const_mul _
  have hfin (n : ℕ) : Continuous (fun π : Good =>
      (quantile ((P π).map (fun w => ∑ k ∈ Finset.range n, γ ^ k * reward π k w)) τ).toReal) := by
    let Obs := (k : Fin n) → (Fin (k.val + 1) → S) → A
    let observe : Good → Obs := fun π k => π.val k.val
    let extend : Obs → Policy S A := fun f k h => if hk : k < n then f ⟨k, hk⟩ h else d k h
    let value : Obs → ℝ := fun f =>
      (quantile (rewardLaw (discountedModel M γ) n (extend f) s) τ).toReal
    have hf : Continuous value := continuous_of_discreteTopology
    have ho : Continuous observe :=
      continuous_pi fun k => (continuous_apply k.val).comp continuous_subtype_val
    convert hf.comp ho using 1
    funext π
    change (quantile ((P π).map (fun w => ∑ k ∈ Finset.range n, γ ^ k * reward π k w)) τ).toReal =
      (quantile (rewardLaw (discountedModel M γ) n (extend (observe π)) s) τ).toReal
    rw [path_map_partial_reward M π.val s (P π) (hP π) γ n,
      prefix_policy_rewardLaw (discountedModel M γ) n π.val (extend (observe π)) s]
    intro k hk
    funext h
    simp [extend, observe, hk]
  have hpay (π : Good) (k : ℕ) (w : ℕ → S) : |reward π k w| ≤ R := hR k _ _ _
  have hreal (π : Good) (n : ℕ) :
      ∃ x : ℝ, quantile ((P π).map (fun w => ∑ k ∈ Finset.range n, γ ^ k * reward π k w)) τ =
        (x : EReal) := by
    let := hp π
    apply quantile_map_real_of_bounded (P π) _ (hpartial π n)
      (∑ k ∈ Finset.range n, γ ^ k * R) τ _ hτ
    intro w
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hγ₀ k)]
      exact mul_le_mul_of_nonneg_left (hpay π k w) (pow_nonneg hγ₀ k))
  have hreal' (π : Good) :
      ∃ x : ℝ, quantile ((P π).map (fun w => ∑' k, γ ^ k * reward π k w)) τ = (x : EReal) := by
    let := hp π
    apply quantile_map_real_of_bounded (P π) _ (hfull π)
      (R / (1 - γ)) τ _ hτ
    intro w
    simpa using discounted_truncation_bound (fun k => reward π k w) γ R hγ₀ hγ₁
      (fun k => hpay π k w) 0
  exact infinite_optimal_of_compact P hp reward γ R hγ₀ hγ₁ hpay τ hpartial hfull hfin hreal hreal'

end QuantileMDP

open MeasureTheory Filter
open scoped Topology

namespace QuantileMDP

/-- Discounted backward values converge to the infinite-horizon optimal
quantile, with a uniform geometric error. The model may be time dependent. -/
theorem theorem_6_discounted_limit {S A : Type*} [Fintype S] [Fintype A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S A)
    (γ R : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hR : ∀ k s a i, |M.r k s a i| ≤ R)
    (s : S) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let V := ⨆ π : {π : Policy S A // M.Admissible π},
      quantile ((trajectoryLaw M π.val s).map (fun w => ∑' k, γ ^ k * stepReward M π.val k w)) τ
    Tendsto (fun n => dpValue (discountedModel M γ) n 0 s τ) atTop (𝓝 V) ∧
      ∀ n, dpValue (discountedModel M γ) n 0 s τ ≤ V + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) ∧
        V ≤ dpValue (discountedModel M γ) n 0 s τ + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) :=
  discounted_mdp_value_limit M (fun x π => trajectoryLaw M π.val x)
    (fun x π => trajectoryLaw_isPolicyPathLaw M π.val x) γ R hγ₀ hγ₁ hR s τ hτ

/-- Stationary value iteration converges at a geometric rate, and its
limit is attained by an admissible history-dependent policy. -/
theorem verified_theorem_6_stationary {S A : Type*} [Fintype S] [Fintype A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S A)
    (hP : ∀ k, M.P k = M.P 0) (hr : ∀ k, M.r k = M.r 0) (ha : ∀ k, M.adm k = M.adm 0)
    (γ R : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hR : ∀ k s a i, |M.r k s a i| ≤ R)
    (s : S) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let Q := fun π : {π : Policy S A // M.Admissible π} =>
      quantile ((trajectoryLaw M π.val s).map (fun w => ∑' k, γ ^ k * stepReward M π.val k w)) τ
    let V := ⨆ π, Q π
    (∃ π, Q π = V) ∧ Tendsto (fun n => discountedIter M γ n s τ) atTop (𝓝 V) ∧
      ∀ n, discountedIter M γ n s τ ≤ V + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) ∧
        V ≤ discountedIter M γ n s τ + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) := by
  dsimp only
  simp_rw [discountedIter_eq_dpValue M hP hr ha γ hγ₀]
  exact ⟨infinite_optimal_exists M s (fun π => trajectoryLaw M π.val s)
    (fun π => trajectoryLaw_isPolicyPathLaw M π.val s) γ R hγ₀.le hγ₁ hR τ hτ,
    theorem_6_discounted_limit M γ R hγ₀.le hγ₁ hR s τ hτ⟩

end QuantileMDP

open QuantileMDP

theorem solution {S A : Type*} [Fintype S] [Fintype A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S A)
    (hP : ∀ k, M.P k = M.P 0) (hr : ∀ k, M.r k = M.r 0) (ha : ∀ k, M.adm k = M.adm 0)
    (γ R : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hR : ∀ k s a i, |M.r k s a i| ≤ R)
    (s : S) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let Q := fun π : {π : Policy S A // M.Admissible π} =>
      quantile ((trajectoryLaw M π.val s).map (fun w => ∑' k, γ ^ k * stepReward M π.val k w)) τ
    let V := ⨆ π, Q π
    (∃ π, Q π = V) ∧ Tendsto (fun n => discountedIter M γ n s τ) atTop (𝓝 V) ∧
      ∀ n, discountedIter M γ n s τ ≤ V + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) ∧
        V ≤ discountedIter M γ n s τ + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) := QuantileMDP.verified_theorem_6_stationary M hP hr ha γ R hγ₀ hγ₁ hR s τ hτ
