-- Prove2me | solution 1 for TPG.proposition_4_general_bernoulli
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:39:12.518043+00:00
-- url     : https://prove2.me/submissions/788e3989-6cda-4b24-84b8-be3347ab3700

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge
import Theorems.Thm_TPG_integral_tpgEst
import Theorems.Thm_TPG_integral_cond_Z
import Theorems.Thm_TPG_integral_Y_trajLaw
import Theorems.Thm_TPG_hasDerivAt_meanReward

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_P4

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

/-- The state distribution at time `t` when the treatment probability is `θ` before time `a`
and `q` from time `a` on factors through the state distribution at time `a` under `π_θ`. -/
lemma stateVec_split {S : Type} [Fintype S] [DecidableEq S] (E : Env S) (θ q : ℝ) (a t : ℕ)
    (h : a ≤ t) :
    E.stateVec (fun s => if a ≤ s then q else θ) t
      = Matrix.vecMul (E.stateDist θ a) (E.PProd q a t) := by
  have h1 : (List.Ico 0 a).map (fun s => E.PMix (if a ≤ s then q else θ) s)
      = (List.Ico 0 a).map (fun u => E.PMix θ u) :=
    List.map_congr_left fun s hs => by
      have hs' := (List.Ico.mem.1 hs).2
      rw [if_neg (by omega)]
  have h2 : (List.Ico a t).map (fun s => E.PMix (if a ≤ s then q else θ) s)
      = (List.Ico a t).map (fun u => E.PMix q u) :=
    List.map_congr_left fun s hs => by
      rw [if_pos (List.Ico.mem.1 hs).1]
  have hr : List.range t = List.Ico 0 a ++ List.Ico a t := by
    rw [List.Ico.append_consecutive (Nat.zero_le a) h, List.Ico.zero_bot]
  unfold Env.stateVec Env.stateDist Env.PProd
  rw [hr, List.map_append, List.prod_append, h1, h2, Matrix.vecMul_vecMul]

/-- The hypothetical truncated value as an average of mean rewards under two-level
treatment-probability sequences. -/
lemma JkGen_eq {S : Type} [Fintype S] [DecidableEq S] (E : Env S) (T k : ℕ) (θ q : ℝ) :
    E.JkGen T k θ q = (1 / (T : ℝ)) * ∑ t : Fin T,
      E.meanReward (fun s => if (t : ℕ) - k ≤ s then q else θ) (t : ℕ) := by
  unfold Env.JkGen Env.meanReward
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [stateVec_split E θ q ((t : ℕ) - k) (t : ℕ) (Nat.sub_le _ _)]
  simp only [if_pos (Nat.sub_le (t : ℕ) k)]

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Under Bernoulli(`θ`) randomization, conditioning on the action at time `u` amounts to
setting the treatment probability of time `u` to `1` or `0`. -/
lemma integral_Y_cond [DecidableEq S] (E : Env S) (T : ℕ) (θ M : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hM : E.RewardBound M) (u t : Fin T) (z : Bool) :
    ∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T θ) {ω | Z u ω = z})
      = E.meanReward (Function.update (fun _ => θ) (u : ℕ) (if z then 1 else 0)) (t : ℕ) := by
  have hq : ∀ s : ℕ, 0 ≤ (fun _ : ℕ => θ) s ∧ (fun _ : ℕ => θ) s ≤ 1 :=
    fun _ => ⟨hθ0.le, hθ1.le⟩
  have h1 := integral_cond_Z E T (fun _ => θ) hq u z ⟨hθ0, hθ1⟩ (Y t)
    (measurable_Y t) (integrable_Y_embedPath E M hM t)
  have hq' : ∀ s : ℕ,
      0 ≤ Function.update (fun _ => θ) (u : ℕ) (if z then 1 else 0) s
        ∧ Function.update (fun _ => θ) (u : ℕ) (if z then 1 else 0) s ≤ 1 := by
    intro s
    by_cases hs : s = (u : ℕ)
    · rw [hs, Function.update_self]
      cases z <;> norm_num
    · rw [Function.update_of_ne hs]
      exact ⟨hθ0.le, hθ1.le⟩
  have h2 := integral_Y_trajLaw E T _ hq' M hM t
  have h3 : E.expLaw T θ = E.trajLaw T (fun _ => θ) := rfl
  rw [h3, h1, h2]
  rfl

/-- The difference of truncated `Q`-values in matrix form. -/
lemma Qk_sub [DecidableEq S] (E : Env S) (T k : ℕ) (θ M : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hM : E.RewardBound M) (u : Fin T) :
    E.Qk θ T k u true - E.Qk θ T k u false
      = ∑ t : Fin T, if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
          (E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ)
            - E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ))
        else 0 := by
  have ht : ∀ t : Fin T,
      ∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T θ) {ω | Z u ω = true})
        = E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ) :=
    fun t => integral_Y_cond E T θ M hθ0 hθ1 hM u t true
  have hf : ∀ t : Fin T,
      ∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T θ) {ω | Z u ω = false})
        = E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ) :=
    fun t => integral_Y_cond E T θ M hθ0 hθ1 hM u t false
  unfold Env.Qk
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ht t, hf t]
  by_cases hc : (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k
  · rw [if_pos hc, if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, if_neg hc, sub_zero]

/-- Conjunct (1): the mean of the estimator is the average difference of truncated `Q`-values. -/
lemma integral_tpgEst_eq [DecidableEq S] (E : Env S) (T : ℕ) (θ M : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hM : E.RewardBound M) (k : ℕ) :
    ∫ ω, tpgEst θ T k ω ∂(E.expLaw T θ)
      = (1 / (T : ℝ)) * ∑ u : Fin T, (E.Qk θ T k u true - E.Qk θ T k u false) := by
  rw [integral_tpgEst E T k θ M hθ0 hθ1 hM]
  congr 1
  exact Finset.sum_congr rfl fun u _ => (Qk_sub E T k θ M hθ0 hθ1 hM u).symm

/-- Conjunct (2): the derivative of the hypothetical truncated value at `q = θ`. -/
lemma hasDerivAt_JkGen [DecidableEq S] (E : Env S) (T : ℕ) (θ M : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hM : E.RewardBound M) (k : ℕ) :
    HasDerivAt (fun q : ℝ => E.JkGen T k θ q)
      ((1 / (T : ℝ)) * ∑ u : Fin T, (E.Qk θ T k u true - E.Qk θ T k u false)) θ := by
  have hD : ∀ t : Fin T,
      HasDerivAt
        (fun q : ℝ => E.meanReward (fun s => if (t : ℕ) - k ≤ s then q else θ) (t : ℕ))
        (∑ u ∈ Finset.range ((t : ℕ) + 1),
          if (t : ℕ) - k ≤ u then
            (E.meanReward (Function.update (fun _ => θ) u 1) (t : ℕ)
              - E.meanReward (Function.update (fun _ => θ) u 0) (t : ℕ))
          else 0) θ := by
    intro t
    have h := hasDerivAt_meanReward E (t : ℕ) (fun s => (t : ℕ) - k ≤ s) (fun _ => θ) θ
    simp only [ite_self] at h
    exact h
  have hsum : HasDerivAt
      (fun q : ℝ => (1 / (T : ℝ)) * ∑ t : Fin T,
        E.meanReward (fun s => if (t : ℕ) - k ≤ s then q else θ) (t : ℕ))
      ((1 / (T : ℝ)) * ∑ t : Fin T, ∑ u ∈ Finset.range ((t : ℕ) + 1),
        if (t : ℕ) - k ≤ u then
          (E.meanReward (Function.update (fun _ => θ) u 1) (t : ℕ)
            - E.meanReward (Function.update (fun _ => θ) u 0) (t : ℕ))
        else 0) θ :=
    (HasDerivAt.fun_sum fun t _ => hD t).const_mul _
  have hfun : (fun q : ℝ => E.JkGen T k θ q)
      = (fun q : ℝ => (1 / (T : ℝ)) * ∑ t : Fin T,
        E.meanReward (fun s => if (t : ℕ) - k ≤ s then q else θ) (t : ℕ)) :=
    funext fun q => JkGen_eq E T k θ q
  have hQ : ∑ u : Fin T, (E.Qk θ T k u true - E.Qk θ T k u false)
      = ∑ u : Fin T, ∑ t : Fin T, if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
          (E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ)
            - E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ))
        else 0 :=
    Finset.sum_congr rfl fun u _ => Qk_sub E T k θ M hθ0 hθ1 hM u
  rw [hfun, hQ]
  refine hsum.congr_deriv ?_
  congr 1
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_range_succ_eq_sum_fin T (t : ℕ) t.isLt
    (fun u => E.meanReward (Function.update (fun _ => θ) u 1) (t : ℕ)
      - E.meanReward (Function.update (fun _ => θ) u 0) (t : ℕ)) (fun u => (t : ℕ) - k ≤ u)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hiff : ((u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) - k ≤ (u : ℕ))
      ↔ ((u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k) := by omega
  exact if_congr hiff rfl rfl

/-- Conjunct (3): with truncation size `T` the hypothetical truncated value is the value
function. -/
lemma JkGen_eq_J [DecidableEq S] (E : Env S) (T : ℕ) (θ M : ℝ) (hM : E.RewardBound M)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : E.JkGen T T θ q = E.J T q := by
  rw [JkGen_eq]
  unfold Env.J
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : (t : ℕ) - T = 0 := Nat.sub_eq_zero_of_le t.isLt.le
  have hfun : (fun s : ℕ => if (t : ℕ) - T ≤ s then q else θ) = fun _ => q := by
    funext s
    rw [ht, if_pos (Nat.zero_le s)]
  have h3 : E.expLaw T q = E.trajLaw T (fun _ => q) := rfl
  rw [hfun, h3, integral_Y_trajLaw E T (fun _ => q) (fun _ => ⟨hq0, hq1⟩) M hM t]
  rfl

end TPG_P4

theorem solution {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ M : ℝ)
    (hT : 0 < T) (hk : k ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : E.RewardBound M) :
    (∫ ω, tpgEst θ T k ω ∂(E.expLaw T θ)
        = (1 / (T : ℝ)) * ∑ u : Fin T, (E.Qk θ T k u true - E.Qk θ T k u false))
      ∧ HasDerivAt (fun q : ℝ => E.JkGen T k θ q)
          ((1 / (T : ℝ)) * ∑ u : Fin T, (E.Qk θ T k u true - E.Qk θ T k u false)) θ
      ∧ (∀ q : ℝ, 0 ≤ q → q ≤ 1 → E.JkGen T T θ q = E.J T q)
      ∧ HasDerivAt (fun q : ℝ => E.J T q) (∫ ω, tpgEst θ T T ω ∂(E.expLaw T θ)) θ := by
  have h1 := TPG_P4.integral_tpgEst_eq E T θ M hθ0 hθ1 hM
  have h2 := TPG_P4.hasDerivAt_JkGen E T θ M hθ0 hθ1 hM
  have h3 := TPG_P4.JkGen_eq_J E T θ M hM
  refine ⟨h1 k, h2 k, h3, ?_⟩
  rw [h1 T]
  refine (h2 T).congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hθ0 hθ1] with q hq
  exact (h3 q hq.1 hq.2).symm
