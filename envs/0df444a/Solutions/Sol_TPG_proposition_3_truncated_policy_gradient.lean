-- Prove2me | solution 1 for TPG.proposition_3_truncated_policy_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:27:54.098031+00:00
-- url     : https://prove2.me/submissions/68936a3f-6ac0-46e3-af4a-5c39ff3ae5fc

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge
import Theorems.Thm_TPG_integral_Y_trajLaw
import Theorems.Thm_TPG_integral_cond_Z
import Theorems.Thm_TPG_hasDerivAt_meanReward

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_B2_PG

/-- A sum over `u ≤ t` restricted to a set of indices, rewritten as a sum over `Fin T`. -/
lemma sum_range_succ_eq_sum_fin (T t : ℕ) (ht : t < T) (f : ℕ → ℝ) (p : ℕ → Prop)
    [DecidablePred p] :
    ∑ u ∈ Finset.range (t + 1), (if p u then f u else 0)
      = ∑ u : Fin T, if (u : ℕ) ≤ t ∧ p (u : ℕ) then f (u : ℕ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun u => if u ≤ t ∧ p u then f u else 0) T]
  have hsub : Finset.range (t + 1) ⊆ Finset.range T := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun u hu => ?_
    have hu' : u ≤ t := by
      have := Finset.mem_range.1 hu
      omega
    simp only [hu', true_and]
  · intro u _ hu
    have hu' : ¬ u ≤ t := fun h => hu (Finset.mem_range.2 (by omega))
    simp only [hu', false_and, if_false]

lemma measurable_Y {S : Type} [MeasurableSpace S] {T : ℕ} (t : Fin T) :
    Measurable (Y t : Traj S T → ℝ) := by
  unfold Y
  exact (measurable_pi_apply t).snd.snd

/-- Along a fixed state/action path the reward at time `t` is an integrable coordinate. -/
lemma integrable_Y_embedPath {S : Type} [Fintype S] (E : Env S) (M : ℝ) (hM : E.RewardBound M)
    {T : ℕ} (t : Fin T) (p : (Fin T → S) × (Fin T → Bool)) :
    Integrable (fun y : Fin T → ℝ => Y t (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2) := by
  have hid : ∀ (x : S) (z : Bool), Integrable (id : ℝ → ℝ) (E.R x z) := by
    intro x z
    refine Integrable.of_bound aestronglyMeasurable_id M ?_
    have hae : ∀ᵐ y ∂(E.R x z), y ∈ Set.Icc (-M) M :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).2 (hM x z)
    filter_upwards [hae] with y hy
    rw [id, Real.norm_eq_abs]
    exact abs_le.2 hy
  have hval : ∀ y : Fin T → ℝ, Y t (embedPath p.1 p.2 y) = y t := fun y => rfl
  simp only [hval]
  exact integrable_eval (μ := fun s : Fin T => E.R (p.1 s) (p.2 s)) (i := t) (hid _ _)

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Under Bernoulli(1/2) randomization, conditioning on the action at time `u` amounts to
setting the treatment probability of time `u` to `1` or `0`. -/
lemma integral_Y_cond [DecidableEq S] (E : Env S) (T : ℕ) (M : ℝ) (hM : E.RewardBound M)
    (u t : Fin T) (z : Bool) :
    ∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T (1 / 2)) {ω | Z u ω = z})
      = E.meanReward (Function.update (fun _ => (1 / 2 : ℝ)) (u : ℕ) (if z then 1 else 0))
          (t : ℕ) := by
  have hq : ∀ s : ℕ, 0 ≤ (fun _ : ℕ => (1 / 2 : ℝ)) s ∧ (fun _ : ℕ => (1 / 2 : ℝ)) s ≤ 1 :=
    fun _ => by norm_num
  have h1 := integral_cond_Z E T (fun _ => (1 / 2 : ℝ)) hq u z (by norm_num) (Y t)
    (measurable_Y t) (integrable_Y_embedPath E M hM t)
  have hq' : ∀ s : ℕ,
      0 ≤ Function.update (fun _ => (1 / 2 : ℝ)) (u : ℕ) (if z then 1 else 0) s
        ∧ Function.update (fun _ => (1 / 2 : ℝ)) (u : ℕ) (if z then 1 else 0) s ≤ 1 := by
    intro s
    by_cases hs : s = (u : ℕ)
    · rw [hs, Function.update_self]
      cases z <;> norm_num
    · rw [Function.update_of_ne hs]
      norm_num
  have h2 := integral_Y_trajLaw E T _ hq' M hM t
  have h3 : E.expLaw T (1 / 2) = E.trajLaw T (fun _ => (1 / 2 : ℝ)) := rfl
  rw [h3, h1, h2]
  rfl

/-- Common core of Propositions 1 and 3: the derivative at `1/2` of the average reward when the
action at time `s` influencing the reward at time `t` is treatment with probability `θ` for
`s` in `A t` and with probability `1/2` otherwise. -/
theorem key (E : Env S) (T : ℕ) (M : ℝ) (hM : E.RewardBound M)
    (A : ℕ → ℕ → Prop) [∀ t, DecidablePred (A t)] :
    HasDerivAt (fun θ : ℝ => (1 / (T : ℝ)) * ∑ t : Fin T,
        ∫ ω, Y t ω ∂(E.trajLaw T (fun s => if A (t : ℕ) s then θ else 1 / 2)))
      ((1 / (T : ℝ)) * ∑ u : Fin T, ∑ t : Fin T,
        if (u : ℕ) ≤ (t : ℕ) ∧ A (t : ℕ) (u : ℕ) then
          ((∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T (1 / 2)) {ω | Z u ω = true}))
            - ∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T (1 / 2)) {ω | Z u ω = false}))
        else 0)
      (1 / 2) := by
  classical
  have hD : ∀ t : Fin T,
      HasDerivAt (fun θ : ℝ => E.meanReward (fun s => if A (t : ℕ) s then θ else 1 / 2) (t : ℕ))
        (∑ u ∈ Finset.range ((t : ℕ) + 1),
          if A (t : ℕ) u then
            (E.meanReward (Function.update (fun _ => (1 / 2 : ℝ)) u 1) (t : ℕ)
              - E.meanReward (Function.update (fun _ => (1 / 2 : ℝ)) u 0) (t : ℕ))
          else 0) (1 / 2) := by
    intro t
    have h := hasDerivAt_meanReward E (t : ℕ) (A (t : ℕ)) (fun _ => (1 / 2 : ℝ)) (1 / 2)
    simp only [ite_self] at h
    exact h
  have hsum : HasDerivAt
      (fun θ : ℝ => (1 / (T : ℝ)) * ∑ t : Fin T,
        E.meanReward (fun s => if A (t : ℕ) s then θ else 1 / 2) (t : ℕ))
      ((1 / (T : ℝ)) * ∑ t : Fin T, ∑ u ∈ Finset.range ((t : ℕ) + 1),
        if A (t : ℕ) u then
          (E.meanReward (Function.update (fun _ => (1 / 2 : ℝ)) u 1) (t : ℕ)
            - E.meanReward (Function.update (fun _ => (1 / 2 : ℝ)) u 0) (t : ℕ))
        else 0) (1 / 2) :=
    (HasDerivAt.fun_sum fun t _ => hD t).const_mul _
  have hev : (fun θ : ℝ => (1 / (T : ℝ)) * ∑ t : Fin T,
        ∫ ω, Y t ω ∂(E.trajLaw T (fun s => if A (t : ℕ) s then θ else 1 / 2)))
      =ᶠ[nhds (1 / 2)] (fun θ : ℝ => (1 / (T : ℝ)) * ∑ t : Fin T,
        E.meanReward (fun s => if A (t : ℕ) s then θ else 1 / 2) (t : ℕ)) := by
    filter_upwards [Icc_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)] with θ hθ
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    refine integral_Y_trajLaw E T _ (fun s => ?_) M hM t
    by_cases h : A (t : ℕ) s
    · simp only [if_pos h]
      exact hθ
    · simp only [if_neg h]
      norm_num
  refine (hsum.congr_of_eventuallyEq hev).congr_deriv ?_
  congr 1
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_range_succ_eq_sum_fin T (t : ℕ) t.isLt
    (fun u => E.meanReward (Function.update (fun _ => (1 / 2 : ℝ)) u 1) (t : ℕ)
      - E.meanReward (Function.update (fun _ => (1 / 2 : ℝ)) u 0) (t : ℕ)) (A (t : ℕ))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_Y_cond E T M hM u t true, integral_Y_cond E T M hM u t false]
  simp

end TPG_B2_PG

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (M : ℝ) (hT : 0 < T) (hk : k ≤ T) (hM : E.RewardBound M) :
    HasDerivAt (fun θ : ℝ => E.Jk T k θ)
      ((1 / (T : ℝ)) * ∑ t : Fin T, (E.Qk (1 / 2) T k t true - E.Qk (1 / 2) T k t false))
      (1 / 2) := by
  have h := TPG_B2_PG.key E T M hM (fun t s => ¬ (s + k < t))
  simp only [ite_not] at h
  simp only [not_lt] at h
  have e : (1 / (T : ℝ)) * ∑ t : Fin T, (E.Qk (1 / 2) T k t true - E.Qk (1 / 2) T k t false)
      = (1 / (T : ℝ)) * ∑ u : Fin T, ∑ t : Fin T,
        if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
          ((∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T (1 / 2)) {ω | Z u ω = true}))
            - ∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T (1 / 2)) {ω | Z u ω = false}))
        else 0 := by
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold Env.Qk
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · rfl
    · exact sub_zero 0
  rw [e]
  exact h
