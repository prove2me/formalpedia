-- Prove2me | solution 1 for QuantileMDP.rationalQuantileScan_correct
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-14T03:03:45.095344+00:00
-- url     : https://prove2.me/submissions/ecc18a38-d66a-4465-ac4a-f5872d86de54

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Definitions.Def_QuantileMDP_quantile
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_QuantileMDP_discountedPath
import Theorems.Thm_QuantileMDP_theorem_2
import Definitions.Def_QuantileMDP_trajectory
import Mathlib.Data.Finset.Order
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.ConditionalProbability
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_achievableLaws
import Mathlib.Data.Set.Finite.Lemmas
import Theorems.Thm_QuantileMDP_eq_7
import Definitions.Def_QuantileMDP_upperCVaR
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QuantileMDP_rationalQuantileScan

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

open MeasureTheory
open scoped ENNReal

namespace QuantileMDP

theorem finite_law_apply {ι : Type*} [Fintype ι] (p : ι → ℝ≥0∞) (x : ι → ℝ)
    (B : Set ℝ) (hB : MeasurableSet B) [DecidablePred (· ∈ B)] :
    (∑ i, p i • Measure.dirac (x i)) B = ∑ i, if x i ∈ B then p i else 0 := by
  rw [Measure.finsetSum_apply _ _ _]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
  by_cases hx : x i ∈ B <;> simp [Set.indicator, hx]

theorem quantile_mem_finset_of_finite_law {ι : Type*} [Fintype ι]
    (p : ι → ℝ≥0∞) (hp : ∑ i, p i = 1) (x : ι → ℝ)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 1) :
    quantile (∑ i, p i • Measure.dirac (x i)) τ ∈ Finset.univ.image (fun i => (x i : EReal)) := by
  classical
  let μ := ∑ i, p i • Measure.dirac (x i)
  let C := (Finset.univ.filter (fun i => p i ≠ 0)).image x
  have hnonempty : C.Nonempty := by
    by_contra he
    have hz : ∀ i, p i = 0 := fun i => not_not.mp fun hi =>
      he ⟨x i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩⟩
    simp [hz] at hp
  have hμ (B : Set ℝ) (hB : MeasurableSet B) :=
    finite_law_apply p x B hB
  have hc (i : ι) (hi : p i ≠ 0) : x i ∈ C :=
    Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
  have hc' {y : ℝ} (hy : y ∈ C) : ∃ i, p i ≠ 0 ∧ x i = y := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩
  have hret {y : ℝ} (hy : y ∈ C) (hyq : quantile μ τ = (y : EReal)) :
      quantile μ τ ∈ Finset.univ.image (fun i => (x i : EReal)) := by
    obtain ⟨i, _, rfl⟩ := hc' hy
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hyq.symm⟩
  change quantile μ τ ∈ _
  by_cases h0 : τ = 0
  · let m := C.min' hnonempty
    have hm := Finset.min'_mem C hnonempty
    apply hret hm
    rw [quantile, if_pos h0]
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨y, hy, rfl⟩
      apply EReal.coe_le_coe_iff.mpr
      by_contra! hlt
      obtain ⟨i, hi, hxi⟩ := hc' hm
      have he : μ (Set.Iio y) = 0 := by
        have : IsProbabilityMeasure μ := ⟨by rw [hμ _ MeasurableSet.univ]; simpa using hp⟩
        have ha := prob_add_prob_compl (μ := μ) (measurableSet_Iio (a := y))
        rw [Set.compl_Iio, show μ (Set.Ici y) = 1 from hy] at ha
        simpa using ha
      rw [hμ _ measurableSet_Iio] at he
      have hle := Finset.single_le_sum (f := fun j => if x j ∈ Set.Iio y then p j else 0)
        (fun j _ => bot_le) (Finset.mem_univ i)
      change (if x i ∈ Set.Iio y then p i else 0) ≤ (∑ j, if x j ∈ Set.Iio y then p j else 0) at hle
      rw [if_pos (show x i ∈ Set.Iio y from Set.mem_Iio.mpr (hxi ▸ hlt))] at hle
      have he' : (∑ j, if x j ∈ Set.Iio y then p j else 0) = 0 := he
      rw [he'] at hle
      exact hi (le_antisymm hle bot_le)
    · refine le_sSup ⟨m, ?_, rfl⟩
      change μ (Set.Ici m) = 1
      rw [hμ _ measurableSet_Ici, ← hp]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : p i = 0
      · simp [hi]
      · rw [if_pos (Set.mem_Ici.mpr (Finset.min'_le C _ (hc i hi)))]
  · let e := ENNReal.ofReal τ
    have he0 : 0 < e := ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hτ.1 (Ne.symm h0))
    have he1 : e ≤ 1 := ENNReal.ofReal_le_one.mpr hτ.2
    have hq : quantile μ τ =
        sInf ((fun y : ℝ => (y : EReal)) '' {y : ℝ | e ≤ μ (Set.Iic y)}) := by
      rw [quantile, if_neg h0]
      by_cases h1 : τ = 1
      · subst τ
        rw [if_pos rfl]
        congr 1
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, by simp [e, show μ (Set.Iic y) = 1 from hy], rfl⟩
        · rintro ⟨y, hy, rfl⟩
          have hle : μ (Set.Iic y) ≤ 1 := by
            refine (measure_mono (Set.subset_univ _)).trans ?_
            rw [hμ _ MeasurableSet.univ]
            simpa using hp.le
          refine ⟨y, le_antisymm hle ?_, rfl⟩
          simpa [e] using (show e ≤ μ (Set.Iic y) from hy)
      · rw [if_neg h1]
    let D := C.filter (fun y => e ≤ μ (Set.Iic y))
    have hD : D.Nonempty := by
      let m := C.max' hnonempty
      refine ⟨m, Finset.mem_filter.mpr ⟨Finset.max'_mem C hnonempty, he1.trans_eq ?_⟩⟩
      rw [hμ _ measurableSet_Iic, ← hp]
      symm
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : p i = 0
      · simp [hi]
      · rw [if_pos (Set.mem_Iic.mpr (Finset.le_max' C _ (hc i hi)))]
    let m := D.min' hD
    obtain ⟨hm, hmf⟩ := Finset.mem_filter.mp (Finset.min'_mem D hD)
    apply hret hm
    rw [hq]
    refine le_antisymm ?_ ?_
    · exact sInf_le ⟨m, hmf, rfl⟩
    refine le_sInf ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : e ≤ μ (Set.Iic y) := hy
    let E := C.filter (fun z => z ≤ y)
    have hE : E.Nonempty := by
      by_contra hn
      have hzero : μ (Set.Iic y) = 0 := by
        rw [hμ _ measurableSet_Iic]
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : p i = 0
        · simp [hi]
        · rw [if_neg (show x i ∉ Set.Iic y from fun hiy =>
            hn ⟨x i, Finset.mem_filter.mpr ⟨hc i hi, hiy⟩⟩)]
      exact he0.not_ge (hzero ▸ hy')
    let z := E.max' hE
    have hz := Finset.mem_filter.mp (Finset.max'_mem E hE)
    have heq : μ (Set.Iic y) = μ (Set.Iic z) := by
      rw [hμ _ measurableSet_Iic, hμ _ measurableSet_Iic]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : p i = 0
      · simp [hi]
      · have hiff : x i ∈ Set.Iic y ↔ x i ∈ Set.Iic z :=
          ⟨fun hx => Finset.le_max' E _ (Finset.mem_filter.mpr ⟨hc i hi, hx⟩),
            fun hx => (show x i ≤ z from hx).trans hz.2⟩
        simp [hiff]
    exact EReal.coe_le_coe_iff.mpr
      ((Finset.min'_le D _ (Finset.mem_filter.mpr ⟨hz.1, heq ▸ hy'⟩)).trans hz.2)


end QuantileMDP

end

section

open MeasureTheory
open scoped ENNReal

namespace QuantileMDP

/-- The optimal quantile has an integer value in `[-T R, T R]` when every
reward is an integer bounded by `R`. This bounds the number of distinct value
levels by `2 T R + 1`. -/
theorem dpValue_integer_range {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (r : ℕ → S → A → S → ℤ) (R : ℕ)
    (hr : ∀ k s a i, M.r k s a i = (r k s a i : ℝ))
    (hR : ∀ k s a i, |r k s a i| ≤ (R : ℤ))
    (T : ℕ) (s : S) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ z : ℤ, |z| ≤ (T : ℤ) * (R : ℤ) ∧ dpValue M T 0 s τ = ((z : ℝ) : EReal) := by
  classical
  obtain ⟨π, _, hval⟩ := (theorem_2 M T s τ hτ).1
  let p (g : Fin T → S) := pathWeight M π (Fin.cons s g)
  let x (g : Fin T → S) := pathReward M π (Fin.cons s g)
  let _ : MeasurableSpace S := ⊤
  let _ : MeasurableSingletonClass S := ⟨fun _ => trivial⟩
  let law := trajectoryLaw M π s
  have hlay := trajectoryLaw_isPolicyPathLaw M π s
  let _ : IsProbabilityMeasure law := hlay.1
  have hmap := path_map_partial_reward M π s law hlay 1 T
  have hd : discountedModel M 1 = M := by cases M; simp [discountedModel]
  rw [hd] at hmap
  have hone : (rewardLaw M T π s) Set.univ = 1 := by
    rw [← hmap, Measure.map_apply]
    · simp
    · exact Finset.measurable_fun_sum _ fun k _ => (measurable_stepReward M π k).const_mul _
    · exact MeasurableSet.univ
  have hp : ∑ g, p g = 1 := by
    simpa [rewardLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, p] using hone
  have hm := quantile_mem_finset_of_finite_law p hp x τ hτ
  rw [hval]
  obtain ⟨g, _, hg⟩ := Finset.mem_image.mp hm
  let w : Fin (T + 1) → S := Fin.cons s g
  let z : ℤ := ∑ t : Fin T, r t.val (w t.castSucc) (π t.val (pathPrefix w t)) (w t.succ)
  refine ⟨z, ?_, ?_⟩
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun t _ =>
      hR t.val (w t.castSucc) (π t.val (pathPrefix w t)) (w t.succ)))
  · change quantile (∑ i, p i • Measure.dirac (x i)) τ = _
    rw [← hg]
    congr 1
    unfold x pathReward
    simp [z, w, hr]

/-- All valid quantile levels together use at most `2 T R + 1` values. -/
theorem dpValue_integer_card {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (r : ℕ → S → A → S → ℤ) (R : ℕ)
    (hr : ∀ k s a i, M.r k s a i = (r k s a i : ℝ))
    (hR : ∀ k s a i, |r k s a i| ≤ (R : ℤ))
    (T : ℕ) (s : S) :
    ∃ C : Finset EReal, C.card ≤ 2 * T * R + 1 ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, dpValue M T 0 s τ ∈ C := by
  classical
  let B : ℤ := (T : ℤ) * (R : ℤ)
  let I := Finset.Icc (-B) B
  refine ⟨I.image (fun z : ℤ => ((z : ℝ) : EReal)), Finset.card_image_le.trans ?_, ?_⟩
  · have hcard : I.card = 2 * T * R + 1 := by
      rw [show I = Finset.Icc (-B) B from rfl, Int.card_Icc]
      have he : B + 1 - -B = ((2 * T * R + 1 : ℕ) : ℤ) := by
        push_cast
        unfold B
        ring
      rw [he, Int.toNat_natCast]
    exact hcard.le
  · intro τ hτ
    obtain ⟨z, hz, he⟩ := dpValue_integer_range M r R hr hR T s τ hτ
    exact Finset.mem_image.mpr ⟨z, Finset.mem_Icc.mpr (abs_le.mp hz), he.symm⟩

end QuantileMDP

end

section

namespace QuantileMDP

/-- Combine a fixed first action with separate continuation policies for each successor. -/
noncomputable def splice {S A : Type*} [DecidableEq S]
    (M : Model S A) (t : ℕ) (s : S) (a : A) (ρ : S → Policy S A) : Policy S A
  | 0, h => if h 0 = s then a else (M.adm_nonempty t (h 0)).choose
  | k + 1, h => ρ (h 1) k (Fin.tail h)

theorem splice_admissible {S A : Type*} [DecidableEq S]
    (M : Model S A) (t : ℕ) (s : S) (a : A) (ha : a ∈ M.adm t s)
    (ρ : S → Policy S A) (hρ : ∀ z, (M.shift (t + 1)).Admissible (ρ z)) :
    (M.shift t).Admissible (splice M t s a ρ) := by
  intro k h
  cases k with
  | zero =>
    have hl : Fin.last 0 = 0 := Fin.eq_zero _
    rw [hl]
    by_cases hh : h 0 = s
    · simpa [splice, Model.shift, hh] using ha
    · simpa [splice, Model.shift, hh] using (M.adm_nonempty t (h 0)).choose_spec
  | succ k =>
    simpa [splice, Model.shift, Fin.tail, Nat.add_left_comm, Nat.add_comm] using
      hρ (h 1) k (Fin.tail h)

/-- Reward laws only depend on the policy on histories starting at the given state. -/
theorem rewardLaw_congr_start {S A : Type*} [Fintype S] (M : Model S A)
    (n : ℕ) (π ρ : Policy S A) (s : S)
    (h : ∀ k (g : Fin (k + 1) → S), g 0 = s → π k g = ρ k g) :
    rewardLaw M n π s = rewardLaw M n ρ s := by
  have hp (g : Fin n → S) (i : Fin n) : pathPrefix (Fin.cons s g) i 0 = s := by
    rfl
  unfold rewardLaw
  apply Finset.sum_congr rfl
  intro g _
  have hw : pathWeight M π (Fin.cons s g) = pathWeight M ρ (Fin.cons s g) := by
    unfold pathWeight
    exact Finset.prod_congr rfl fun i _ => by rw [h _ _ (hp g i)]
  have hr : pathReward M π (Fin.cons s g) = pathReward M ρ (Fin.cons s g) := by
    unfold pathReward
    exact Finset.sum_congr rfl fun i _ => by rw [h _ _ (hp g i)]
  rw [hw, hr]

theorem splice_rewardLaw {S A : Type*} [Fintype S] [DecidableEq S]
    (M : Model S A) (t n : ℕ) (s aState : S) (a : A) (ρ : S → Policy S A) :
    rewardLaw (M.shift (t + 1)) n ((splice M t s a ρ).tail s) aState =
      rewardLaw (M.shift (t + 1)) n (ρ aState) aState := by
  apply rewardLaw_congr_start
  intro k g hg
  simpa [Policy.tail, splice, Fin.tail_cons, Fin.cons_succ] using
    congrArg (fun z => ρ z k g) hg

end QuantileMDP

end

section

open MeasureTheory

namespace QuantileMDP

/-- The recursion generates exactly the laws of admissible deterministic
history-dependent policies. -/
theorem mem_achievableLaws_iff {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (s : S) (μ : Measure ℝ) :
    μ ∈ achievableLaws M n t s ↔
      ∃ π : Policy S A, (M.shift t).Admissible π ∧ μ = rewardLaw (M.shift t) n π s := by
  classical
  induction n generalizing t s μ with
  | zero =>
    have hzero (π : Policy S A) : rewardLaw (M.shift t) 0 π s = Measure.dirac 0 := by
      simp [rewardLaw, pathWeight, pathReward]
    simp only [achievableLaws, Set.mem_singleton_iff, hzero]
    constructor
    · intro h
      exact ⟨fun k g => ((M.shift t).adm_nonempty k (g (Fin.last k))).choose,
        fun k g => ((M.shift t).adm_nonempty k (g (Fin.last k))).choose_spec, h⟩
    · exact fun ⟨_, _, h⟩ => h
  | succ n ih =>
    have hlen : t + (n + 1) - t = n + 1 := by omega
    have htail : t + (n + 1) - (t + 1) = n := by omega
    have ht : t < t + (n + 1) := by omega
    have hl (π : Policy S A) (a : A) (hπ : (M.shift t).Admissible π)
        (ha : π 0 (fun _ => s) = a) :
        rewardLaw (M.shift t) (n + 1) π s =
          ∑ i, M.P t s a i • ((rewardLaw (M.shift (t + 1)) n (π.tail s) i).map
            (fun x => x + M.r t s a i)) := by
      simpa only [hlen, htail] using ((eq_7 M (t + (n + 1)) t ht s a).1 π hπ ha)
    change (∃ a ∈ M.adm t s, ∃ ν : S → Measure ℝ,
        (∀ i, ν i ∈ achievableLaws M n (t + 1) i) ∧
          μ = ∑ i, M.P t s a i • (ν i).map (fun x => x + M.r t s a i)) ↔ _
    constructor
    · rintro ⟨a, ha, ν, hν, rfl⟩
      have hρ (i) := (ih (t + 1) i (ν i)).mp (hν i)
      choose ρ hρa hρlaw using hρ
      let π := splice M t s a ρ
      have ha' : π 0 (fun _ => s) = a := by simp [π, splice]
      have hπ := splice_admissible M t s a ha ρ hρa
      refine ⟨π, hπ, ?_⟩
      rw [hl π a hπ ha']
      apply Finset.sum_congr rfl
      intro i _
      rw [hρlaw i, splice_rewardLaw]
    · rintro ⟨π, hπ, rfl⟩
      let a := π 0 (fun _ => s)
      have ha : a ∈ M.adm t s := by simpa [a, Model.shift] using hπ 0 (fun _ => s)
      let ν := fun i => rewardLaw (M.shift (t + 1)) n (π.tail s) i
      refine ⟨a, ha, ν, fun i => (ih (t + 1) i (ν i)).mpr ⟨π.tail s, ?_, rfl⟩, hl π a hπ rfl⟩
      intro k g
      simpa [Policy.tail, Model.shift, Fin.succ_last, Nat.add_left_comm, Nat.add_comm] using
        hπ (k + 1) (Fin.cons s g)

end QuantileMDP

end

section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace QuantileMDP

/-- Backward recursion for the minimum probability of reaching a lower
reward tail. The Boolean selects a closed or open tail. -/
noncomputable def lowerTailDP {S A : Type*} [Fintype S] (M : Model S A) (closed : Bool) :
    ℕ → ℕ → S → ℝ → ℝ≥0∞
  | 0, _, _, x => if (if closed then 0 ≤ x else 0 < x) then 1 else 0
  | n + 1, t, s, x => ⨅ a ∈ M.adm t s, ∑ i, M.P t s a i *
      lowerTailDP M closed n (t + 1) i (x - M.r t s a i)

def tailEvent (closed : Bool) (x : ℝ) : Set ℝ :=
  if closed then Set.Iic x else Set.Iio x

/-- The threshold recursion computes the attained minimum lower-tail
probability over admissible policies. -/
theorem lowerTailDP_isLeast {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (closed : Bool) (n t : ℕ) (s : S) (x : ℝ) :
    IsLeast ((fun μ : Measure ℝ => μ (tailEvent closed x)) '' achievableLaws M n t s)
      (lowerTailDP M closed n t s x) := by
  classical
  induction n generalizing t s x with
  | zero =>
    rw [achievableLaws, Set.image_singleton, lowerTailDP]
    have h : Measure.dirac (0 : ℝ) (tailEvent closed x) = if (if closed then 0 ≤ x else 0 < x) then 1 else 0 := by
      rw [Measure.dirac_apply]
      cases closed <;> simp [tailEvent, Set.indicator]
    rw [← h]
    exact ⟨rfl, fun _ hv => (Set.mem_singleton_iff.mp hv).ge⟩
  | succ n ih =>
    let cdf (a : A) := ∑ i, M.P t s a i * lowerTailDP M closed n (t + 1) i (x - M.r t s a i)
    obtain ⟨a, hadm, hmin⟩ :=
      Set.exists_min_image (M.adm t s) cdf (Set.toFinite _) (M.adm_nonempty t s)
    have hval : lowerTailDP M closed (n + 1) t s x = cdf a := by
      rw [lowerTailDP]
      apply le_antisymm (iInf_le_of_le a (iInf_le _ hadm))
      exact le_iInf fun b => le_iInf fun hb => hmin b hb
    have hmix (b : A) (ν : S → Measure ℝ) :
        (∑ i, M.P t s b i • (ν i).map (fun z => z + M.r t s b i)) (tailEvent closed x) =
          ∑ i, M.P t s b i * ν i (tailEvent closed (x - M.r t s b i)) := by
      rw [Measure.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hm : Measurable (fun z : ℝ => z + M.r t s b i) := measurable_id.add_const _
      have hmeas : MeasurableSet (tailEvent closed x) := by
        cases closed
        · exact measurableSet_Iio
        · exact measurableSet_Iic
      rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm hmeas]
      congr 2
      ext z
      cases closed
      · change z + M.r t s b i < x ↔ z < x - M.r t s b i
        exact lt_sub_iff_add_lt.symm
      · change z + M.r t s b i ≤ x ↔ z ≤ x - M.r t s b i
        exact le_sub_iff_add_le.symm
    constructor
    · have he (i : S) := (ih (t + 1) i (x - M.r t s a i)).1
      choose ν hν hv using he
      refine ⟨∑ i, M.P t s a i • (ν i).map (fun z => z + M.r t s a i),
        ⟨a, hadm, ν, hν, rfl⟩, ?_⟩
      dsimp only
      rw [hmix, hval]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun v => M.P t s a i * v) (hv i)
    · rintro _ ⟨μ, ⟨b, hb, ν, hν, rfl⟩, rfl⟩
      dsimp only
      rw [hmix, hval]
      refine (hmin b hb).trans (Finset.sum_le_sum fun i _ => ?_)
      exact mul_le_mul_of_nonneg_left
        ((ih (t + 1) i (x - M.r t s b i)).2 ⟨ν i, hν i, rfl⟩) bot_le

end QuantileMDP

namespace QuantileMDP

private theorem tendsto_closed_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    Tendsto (fun y => μ (Iic y)) (𝓝[>] x) (𝓝 (μ (Iic x))) := by
  have hset : (⋂ y > x, Iic y) = Iic x := by
    ext z
    simp only [mem_iInter, mem_Iic]
    exact ⟨fun h => le_of_not_gt fun hz =>
      let ⟨y, hxy, hyz⟩ := exists_between hz
      (not_le_of_gt hyz) (h y hxy), fun h y hy => h.trans hy.le⟩
  rw [← hset]
  exact tendsto_measure_biInter_gt (fun _ _ => measurableSet_Iic.nullMeasurableSet)
    (fun _ _ _ h => Iic_subset_Iic.mpr h) ⟨x + 1, by linarith, measure_ne_top μ _⟩

private theorem positive_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    quantile μ τ ≤ (x : EReal) ↔ ENNReal.ofReal τ ≤ μ (Iic x) := by
  have hdef : quantile μ τ =
      sInf ((fun y : ℝ => (y : EReal)) '' {y : ℝ | ENNReal.ofReal τ ≤ μ (Iic y)}) := by
    rw [quantile, if_neg hτ.ne']
    split_ifs with he
    · subst τ
      congr 2
      ext y
      simp only [mem_ofPred_eq, ENNReal.ofReal_one]
      exact ⟨fun h => h.ge, fun h => le_antisymm prob_le_one h⟩
    · rfl
  rw [hdef]
  refine ⟨?_, fun hx => sInf_le ⟨x, hx, rfl⟩⟩
  intro hx
  by_contra! h
  have he := (tendsto_order.mp (tendsto_closed_tail μ x)).2 _ h
  obtain ⟨y, hy, hyx⟩ := (he.and (@self_mem_nhdsWithin _ _ x (Ioi x))).exists
  have hyinf : (y : EReal) ≤ sInf ((fun z : ℝ => (z : EReal)) ''
      {z : ℝ | ENNReal.ofReal τ ≤ μ (Iic z)}) := by
    refine le_sInf ?_
    rintro _ ⟨z, hz, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (le_of_not_gt fun hzy =>
      (not_le_of_gt hy) (hz.trans (measure_mono (Iic_subset_Iic.mpr hzy.le))))
  exact (not_le_of_gt (EReal.coe_lt_coe_iff.mpr hyx)) (hyinf.trans hx)

private theorem finiteRewardLaw_isProbabilityMeasure {S A : Type*} [Fintype S]
    (M : Model S A) (T : ℕ) (π : Policy S A) (s : S) :
    IsProbabilityMeasure (rewardLaw M T π s) := by
  let _ : MeasurableSpace S := ⊤
  let _ : MeasurableSingletonClass S := ⟨fun _ => trivial⟩
  let P := trajectoryLaw M π s
  have hP := trajectoryLaw_isPolicyPathLaw M π s
  let _ : IsProbabilityMeasure P := hP.1
  have hd : discountedModel M 1 = M := by cases M; simp [discountedModel]
  rw [← hd, ← path_map_partial_reward M π s P hP 1 T]
  exact Measure.isProbabilityMeasure_map
    (Finset.measurable_fun_sum _ fun k _ => (measurable_stepReward M π k).const_mul _).aemeasurable

/-- The same threshold recursion detects whether the optimal positive-level
quantile exceeds a specified threshold. -/
theorem lt_dpValue_iff_lowerTailDP_lt {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (T : ℕ) (s : S) (x τ : ℝ) (hτ : τ ∈ Set.Ioc (0 : ℝ) 1) :
    (x : EReal) < dpValue M T 0 s τ ↔ lowerTailDP M true T 0 s x < ENNReal.ofReal τ := by
  have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2⟩
  have hs : M.shift 0 = M := by cases M; simp [Model.shift]
  have hgreat := theorem_2 M T s τ hτ'
  have hleast := lowerTailDP_isLeast M true T 0 s x
  constructor
  · intro hv
    obtain ⟨π, hπ, hq⟩ := hgreat.1
    have hm := (mem_achievableLaws_iff M T 0 s (rewardLaw M T π s)).mpr
      ⟨π, by simpa only [hs] using hπ, by rw [hs]⟩
    refine (hleast.2 ⟨_, hm, rfl⟩).trans_lt (lt_of_not_ge ?_)
    intro hc
    rw [hq] at hv
    let _ := finiteRewardLaw_isProbabilityMeasure M T π s
    exact hv.not_ge ((positive_quantile (rewardLaw M T π s) hτ.1 x).mpr hc)
  · intro hv
    obtain ⟨μ, hμ, hc⟩ := hleast.1
    obtain ⟨π, hπ, rfl⟩ := (mem_achievableLaws_iff M T 0 s μ).mp hμ
    rw [hs] at hπ hc
    refine lt_of_lt_of_le ?_ (hgreat.2 ⟨π, hπ, rfl⟩)
    by_contra! hq
    let _ := finiteRewardLaw_isProbabilityMeasure M T π s
    have hl := (positive_quantile (rewardLaw M T π s) hτ.1 x).mp hq
    exact hv.not_ge (hc ▸ hl)

/-- At level zero a threshold is guaranteed exactly when the smallest
open lower-tail probability is zero. -/
theorem coe_le_dpValue_zero_iff_lowerTailDP_eq_zero {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (T : ℕ) (s : S) (x : ℝ) :
    (x : EReal) ≤ dpValue M T 0 s 0 ↔ lowerTailDP M false T 0 s x = 0 := by
  have hτ : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hs : M.shift 0 = M := by cases M; simp [Model.shift]
  have hgreat := theorem_2 M T s 0 hτ
  have hleast := lowerTailDP_isLeast M false T 0 s x
  have hq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
      (x : EReal) ≤ quantile μ 0 ↔ μ (Set.Iio x) = 0 := by
    have hzero (y : ℝ) : μ (Set.Ici y) = 1 ↔ μ (Set.Iio y) = 0 := by
      have had := prob_add_prob_compl (μ := μ) (measurableSet_Iio (a := y))
      rw [compl_Iio] at had
      constructor
      · intro h
        rw [h] at had
        exact (ENNReal.add_left_inj (by simp : (1 : ℝ≥0∞) ≠ ⊤)).mp (had.trans (zero_add _).symm)
      · intro h
        simpa [h] using had
    rw [quantile, if_pos rfl]
    constructor
    · intro hx
      let y (n : ℕ) := x - 1 / ((n : ℝ) + 1)
      have hy (n : ℕ) : y n < x := by unfold y; exact sub_lt_self _ (by positivity)
      have hmass (n : ℕ) : μ (Iio (y n)) = 0 := by
        have hlt := (EReal.coe_lt_coe_iff.mpr (hy n)).trans_le hx
        obtain ⟨_, ⟨z, hz, rfl⟩, hyz⟩ := lt_sSup_iff.mp hlt
        exact measure_mono_null (Iio_subset_Iio (EReal.coe_lt_coe_iff.mp hyz).le) ((hzero z).mp hz)
      have heq : (⋃ n, Iio (y n)) = Iio x := by
        ext z
        simp only [mem_iUnion, mem_Iio]
        refine ⟨fun ⟨n, hn⟩ => hn.trans (hy n), fun hz => ?_⟩
        obtain ⟨n, hn⟩ := exists_nat_gt ((x - z)⁻¹)
        refine ⟨n, ?_⟩
        have hpos : (0 : ℝ) < n + 1 := by positivity
        have hn' : (x - z)⁻¹ < (n : ℝ) + 1 := by linarith
        have hle : 1 / ((n : ℝ) + 1) < x - z := by
          rw [div_lt_iff₀ hpos]
          simpa [mul_comm] using (inv_lt_iff_one_lt_mul₀ (sub_pos.mpr hz)).mp hn'
        change z < x - 1 / ((n : ℝ) + 1)
        linarith
      rw [← heq]
      exact measure_iUnion_null hmass
    · intro h
      exact le_sSup ⟨x, (hzero x).mpr h, rfl⟩
  constructor
  · intro hx
    obtain ⟨π, hπ, hv⟩ := hgreat.1
    have hm := (mem_achievableLaws_iff M T 0 s (rewardLaw M T π s)).mpr
      ⟨π, by simpa only [hs] using hπ, by rw [hs]⟩
    rw [hv] at hx
    let _ := finiteRewardLaw_isProbabilityMeasure M T π s
    exact le_antisymm ((hleast.2 ⟨_, hm, rfl⟩).trans_eq ((hq _).mp hx)) bot_le
  · intro hx
    obtain ⟨μ, hμ, hc⟩ := hleast.1
    obtain ⟨π, hπ, rfl⟩ := (mem_achievableLaws_iff M T 0 s μ).mp hμ
    rw [hs] at hπ hc
    let _ := finiteRewardLaw_isProbabilityMeasure M T π s
    exact ((hq _).mpr (hc.trans hx)).trans (hgreat.2 ⟨π, hπ, rfl⟩)

end QuantileMDP

end

section

open MeasureTheory
open scoped ENNReal

namespace QuantileMDP

/-- At positive levels, the optimal integer reward is the first integer
threshold whose minimum lower-tail probability reaches the specified level. -/
theorem dpValue_integer_threshold {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (r : ℕ → S → A → S → ℤ) (R : ℕ)
    (hr : ∀ k s a i, M.r k s a i = (r k s a i : ℝ))
    (hR : ∀ k s a i, |r k s a i| ≤ (R : ℤ))
    (T : ℕ) (s : S) (τ : ℝ) (hτ : τ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ z : ℤ, |z| ≤ (T : ℤ) * (R : ℤ) ∧ dpValue M T 0 s τ = ((z : ℝ) : EReal) ∧
      IsLeast {y : ℤ | ENNReal.ofReal τ ≤ lowerTailDP M true T 0 s (y : ℝ)} z := by
  obtain ⟨z, hz, hval⟩ := dpValue_integer_range M r R hr hR T s τ ⟨hτ.1.le, hτ.2⟩
  have hchar (y : ℤ) : ENNReal.ofReal τ ≤ lowerTailDP M true T 0 s (y : ℝ) ↔ z ≤ y := by
    rw [← not_lt, ← lt_dpValue_iff_lowerTailDP_lt M T s _ τ hτ, hval, not_lt,
      EReal.coe_le_coe_iff]
    exact Int.cast_le
  exact ⟨z, hz, hval, (hchar z).mpr le_rfl, fun y hy => (hchar y).mp hy⟩

end QuantileMDP

namespace QuantileMDP

/-- Scanning a bounded integer interval recovers the finite-horizon
optimal quantile. The zero level uses the open tail and a maximum;
positive levels use the closed tail and a minimum. -/
theorem dpValue_integer_scan {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (r : ℕ → S → A → S → ℤ) (R : ℕ)
    (hr : ∀ k s a i, M.r k s a i = (r k s a i : ℝ))
    (hR : ∀ k s a i, |r k s a i| ≤ (R : ℤ))
    (T : ℕ) (s : S) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let B : ℤ := (T : ℤ) * (R : ℤ)
    ∃ z : ℤ, dpValue M T 0 s τ = ((z : ℝ) : EReal) ∧
      (if τ = 0 then
        IsGreatest {y : ℤ | y ∈ Set.Icc (-B) B ∧ lowerTailDP M false T 0 s (y : ℝ) = 0} z
       else
        IsLeast {y : ℤ | y ∈ Set.Icc (-B) B ∧
          ENNReal.ofReal τ ≤ lowerTailDP M true T 0 s (y : ℝ)} z) := by
  dsimp only
  by_cases h0 : τ = 0
  · subst τ
    simp only
    obtain ⟨z, hz, hval⟩ := dpValue_integer_range M r R hr hR T s 0 hτ
    have htest (y : ℤ) : lowerTailDP M false T 0 s (y : ℝ) = 0 ↔ y ≤ z := by
      rw [← coe_le_dpValue_zero_iff_lowerTailDP_eq_zero, hval, EReal.coe_le_coe_iff]
      exact Int.cast_le
    exact ⟨z, hval, ⟨abs_le.mp hz, (htest z).mpr le_rfl⟩, fun y hy => (htest y).mp hy.2⟩
  · simp only [if_neg h0]
    have hτ' : τ ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hτ.1 (Ne.symm h0), hτ.2⟩
    obtain ⟨z, hz, hval, hleast⟩ := dpValue_integer_threshold M r R hr hR T s τ hτ'
    exact ⟨z, hval, ⟨abs_le.mp hz, hleast.1⟩, fun _ hy => hleast.2 hy.2⟩

end QuantileMDP

end

section

open scoped ENNReal

namespace QuantileMDP

private theorem rationalTail_nonneg {S A : Type*} [Fintype S] (actions : ℕ → S → Finset A)
    (hne : ∀ t s, (actions t s).Nonempty) (p : ℕ → S → A → S → ℚ)
    (hp : ∀ t s a i, 0 ≤ p t s a i) (r : ℕ → S → A → S → ℤ) (closed : Bool)
    (n t : ℕ) (s : S) (x : ℤ) : 0 ≤ rationalTail actions hne p r closed n t s x := by
  induction n generalizing t s x with
  | zero => cases closed <;> simp only [rationalTail, Bool.false_eq_true, if_false, if_true] <;> split <;> norm_num
  | succ n ih =>
    rw [rationalTail]
    exact Finset.le_inf' (hne t s) _ fun a _ =>
      Finset.sum_nonneg fun i _ => mul_nonneg (hp t s a i) (ih (t + 1) i _)

theorem rationalTail_eq_lowerTailDP {S A : Type*} [Fintype S] (M : Model S A)
    (actions : ℕ → S → Finset A) (hne : ∀ t s, (actions t s).Nonempty)
    (ha : ∀ t s a, a ∈ actions t s ↔ a ∈ M.adm t s)
    (p : ℕ → S → A → S → ℚ) (hp : ∀ t s a i, 0 ≤ p t s a i)
    (hprob : ∀ t s a i, ENNReal.ofReal (p t s a i : ℝ) = M.P t s a i)
    (r : ℕ → S → A → S → ℤ) (hr : ∀ t s a i, M.r t s a i = (r t s a i : ℝ))
    (closed : Bool) (n t : ℕ) (s : S) (x : ℤ) :
    ENNReal.ofReal (rationalTail actions hne p r closed n t s x : ℝ) =
      lowerTailDP M closed n t s (x : ℝ) := by
  classical
  induction n generalizing t s x with
  | zero =>
    cases closed <;> simp [rationalTail, lowerTailDP] <;> split <;> simp
  | succ n ih =>
    let f (a : A) := ∑ i, p t s a i *
      rationalTail actions hne p r closed n (t + 1) i (x - r t s a i)
    have he (a : A) : ENNReal.ofReal (f a : ℝ) =
        ∑ i, M.P t s a i * lowerTailDP M closed n (t + 1) i ((x : ℝ) - M.r t s a i) := by
      unfold f
      push_cast
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (Rat.cast_nonneg.mpr (hp t s a i)), hprob,
          ih (t + 1) i, Int.cast_sub, hr]
      · exact fun i _ => mul_nonneg (Rat.cast_nonneg.mpr (hp t s a i))
          (Rat.cast_nonneg.mpr (rationalTail_nonneg actions hne p hp r closed n (t + 1) i _))
    rw [rationalTail, lowerTailDP]
    change ENNReal.ofReal (Rat.cast ((actions t s).inf' (hne t s) f)) = _
    obtain ⟨a, hmem, hmin⟩ := (actions t s).exists_min_image f (hne t s)
    have hinf : (actions t s).inf' (hne t s) f = f a := by
      exact le_antisymm (Finset.inf'_le f hmem) (Finset.le_inf' (hne t s) f hmin)
    rw [hinf, he a]
    apply le_antisymm
    · exact le_iInf fun b => le_iInf fun hb => by
        rw [← he a, ← he b]
        exact ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr (hmin b ((ha t s b).mpr hb)))
    · exact iInf_le_of_le a (iInf_le _ ((ha t s a).mp hmem))

private theorem mem_integerGrid (B : ℕ) (y : ℤ) :
    y ∈ integerGrid B ↔ y ∈ Set.Icc (-(B : ℤ)) (B : ℤ) := by
  simp only [integerGrid, Finset.mem_image, Finset.mem_range, Set.mem_Icc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨(y + (B : ℤ)).toNat, ?_, ?_⟩ <;> omega

/-- The executable rational scan returns the same value as the
finite-horizon quantile Bellman recursion, including levels zero and one. -/
theorem verified_rationalQuantileScan_correct {S A : Type*} [Fintype S] (M : Model S A) [Fintype A]
    (actions : ℕ → S → Finset A) (hne : ∀ t s, (actions t s).Nonempty)
    (ha : ∀ t s a, a ∈ actions t s ↔ a ∈ M.adm t s)
    (p : ℕ → S → A → S → ℚ) (hp : ∀ t s a i, 0 ≤ p t s a i)
    (hprob : ∀ t s a i, ENNReal.ofReal (p t s a i : ℝ) = M.P t s a i)
    (r : ℕ → S → A → S → ℤ) (hr : ∀ t s a i, M.r t s a i = (r t s a i : ℝ))
    (R : ℕ) (hR : ∀ t s a i, |r t s a i| ≤ (R : ℤ))
    (T : ℕ) (s : S) (τ : ℚ) (hτ : (τ : ℝ) ∈ Set.Icc 0 1) :
    ∃ z : ℤ, rationalQuantileScan actions hne p r R T s τ = some z ∧
      dpValue M T 0 s (τ : ℝ) = ((z : ℝ) : EReal) := by
  classical
  obtain ⟨z, hval, hscan⟩ := dpValue_integer_scan M r R hr hR T s (τ : ℝ) hτ
  refine ⟨z, ?_, hval⟩
  let I := integerGrid (T * R)
  have hI (y : ℤ) :
      y ∈ I ↔ y ∈ Set.Icc (-((T : ℤ) * (R : ℤ))) ((T : ℤ) * (R : ℤ)) := by
    simpa [I, Int.natCast_mul] using mem_integerGrid (T * R) y
  let v (closed : Bool) (y : ℤ) := rationalTail actions hne p r closed T 0 s y
  have he (closed : Bool) (y : ℤ) : ENNReal.ofReal (v closed y : ℝ) =
      lowerTailDP M closed T 0 s (y : ℝ) :=
    rationalTail_eq_lowerTailDP M actions hne ha p hp hprob r hr closed T 0 s y
  by_cases hz : τ = 0
  · subst τ
    simp only [Rat.cast_zero] at hscan
    let J := I.filter (fun y => v false y = 0)
    have hm (y : ℤ) : y ∈ J ↔ y ∈ I ∧ lowerTailDP M false T 0 s (y : ℝ) = 0 := by
      rw [Finset.mem_filter, ← he]
      apply and_congr_right
      intro _
      rw [ENNReal.ofReal_eq_zero]
      exact ⟨fun hz => by simp [hz], fun hv =>
        le_antisymm (Rat.cast_nonpos.mp hv) (rationalTail_nonneg actions hne p hp r false T 0 s y)⟩
    have hnon : J.Nonempty := ⟨z, (hm z).mpr ⟨(hI z).mpr hscan.1.1, hscan.1.2⟩⟩
    have hmax : J.max' hnon = z := (Finset.max'_eq_iff _ _ _).mpr
      ⟨(hm z).mpr ⟨(hI z).mpr hscan.1.1, hscan.1.2⟩,
        fun y hy => hscan.2 ⟨(hI y).mp ((hm y).mp hy).1, ((hm y).mp hy).2⟩⟩
    have hJ : J.max = (z : WithBot ℤ) := by rw [← Finset.coe_max' hnon, hmax]
    have hJ' : maxOption J = some z := hJ
    simpa only [rationalQuantileScan, if_true] using hJ'
  · have hz' : (τ : ℝ) ≠ 0 := by exact_mod_cast hz
    simp only [if_neg hz'] at hscan
    let J := I.filter (fun y => τ ≤ v true y)
    have hm (y : ℤ) : y ∈ J ↔ y ∈ I ∧ ENNReal.ofReal (τ : ℝ) ≤ lowerTailDP M true T 0 s (y : ℝ) := by
      rw [Finset.mem_filter, ← he]
      apply and_congr_right
      intro _
      rw [ENNReal.ofReal_le_ofReal_iff (Rat.cast_nonneg.mpr
        (rationalTail_nonneg actions hne p hp r true T 0 s y))]
      exact Rat.cast_le.symm
    have hnon : J.Nonempty := ⟨z, (hm z).mpr ⟨(hI z).mpr hscan.1.1, hscan.1.2⟩⟩
    have hmin : J.min' hnon = z := (Finset.min'_eq_iff _ _ _).mpr
      ⟨(hm z).mpr ⟨(hI z).mpr hscan.1.1, hscan.1.2⟩,
        fun y hy => hscan.2 ⟨(hI y).mp ((hm y).mp hy).1, ((hm y).mp hy).2⟩⟩
    have hJ : J.min = (z : WithTop ℤ) := by rw [← Finset.coe_min' hnon, hmin]
    have hJ' : minOption J = some z := hJ
    simpa only [rationalQuantileScan, if_neg hz] using hJ'

end QuantileMDP

end

open scoped ENNReal

open QuantileMDP

theorem solution {S A : Type*} [Fintype S] (M : Model S A) [Fintype A]
    (actions : ℕ → S → Finset A) (hne : ∀ t s, (actions t s).Nonempty)
    (ha : ∀ t s a, a ∈ actions t s ↔ a ∈ M.adm t s)
    (p : ℕ → S → A → S → ℚ) (hp : ∀ t s a i, 0 ≤ p t s a i)
    (hprob : ∀ t s a i, ENNReal.ofReal (p t s a i : ℝ) = M.P t s a i)
    (r : ℕ → S → A → S → ℤ) (hr : ∀ t s a i, M.r t s a i = (r t s a i : ℝ))
    (R : ℕ) (hR : ∀ t s a i, |r t s a i| ≤ (R : ℤ))
    (T : ℕ) (s : S) (τ : ℚ) (hτ : (τ : ℝ) ∈ Set.Icc 0 1) :
    ∃ z : ℤ, rationalQuantileScan actions hne p r R T s τ = some z ∧
      dpValue M T 0 s (τ : ℝ) = ((z : ℝ) : EReal) := verified_rationalQuantileScan_correct M actions hne ha p hp hprob r hr R hR T s τ hτ
