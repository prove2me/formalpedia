-- Prove2me | solution 1 for TPG.integral_rcEst
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:23:03.037895+00:00
-- url     : https://prove2.me/submissions/ede308ea-de61-4021-a1cc-893b8f97db6f

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge
import Theorems.Thm_TPG_integral_trajLaw
import Theorems.Thm_TPG_integral_Y_trajLaw
import Theorems.Thm_TPG_integral_indicator_Z_mul

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_B1_rc

lemma measurable_Z {S : Type} [MeasurableSpace S] {T : ℕ} (u : Fin T) :
    Measurable (Z u : Traj S T → Bool) := by
  unfold Z
  exact (measurable_pi_apply u).snd.fst

lemma measurable_Y {S : Type} [MeasurableSpace S] {T : ℕ} (t : Fin T) :
    Measurable (Y t : Traj S T → ℝ) := by
  unfold Y
  exact (measurable_pi_apply t).snd.snd

/-- Changing one entry of a `[0, 1]`-valued sequence to a value in `[0, 1]` keeps it
`[0, 1]`-valued. -/
lemma update_mem (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (u : ℕ) (a : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1) :
    ∀ t : ℕ, 0 ≤ Function.update q u a t ∧ Function.update q u a t ≤ 1 := by
  intro t
  by_cases h : t = u
  · subst h
    rw [Function.update_self]
    exact ha
  · rw [Function.update_of_ne h]
    exact hq t

/-- Bounded rewards are integrable along every state/action path. -/
lemma integrable_Y_path {S : Type} [Fintype S] (E : Env S) {T : ℕ} (M : ℝ) (hM : E.RewardBound M) (t : Fin T)
    (p : (Fin T → S) × (Fin T → Bool)) :
    Integrable (fun y : Fin T → ℝ => Y t (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2) := by
  have hid : Integrable (id : ℝ → ℝ) (E.R (p.1 t) (p.2 t)) := by
    refine Integrable.of_bound aestronglyMeasurable_id M ?_
    have hae : ∀ᵐ y ∂(E.R (p.1 t) (p.2 t)), y ∈ Set.Icc (-M) M :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).2 (hM (p.1 t) (p.2 t))
    filter_upwards [hae] with y hy
    rw [id, Real.norm_eq_abs]
    exact abs_le.2 hy
  have hval : ∀ y : Fin T → ℝ, Y t (embedPath p.1 p.2 y) = y t := fun y => rfl
  simp only [hval]
  exact integrable_eval (μ := fun s : Fin T => E.R (p.1 s) (p.2 s)) (i := t) hid

/-- **Reweighting identity.** Weighting by a function `w` of the action at time `u` splits an
expectation according to the value of `Z u`; on each part the law is the one that forces that
action at time `u`. -/
lemma integral_weight_mul {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (w : Bool → ℝ) (u : Fin T) (G : Traj S T → ℝ) (hG : Measurable G)
    (hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => G (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2)) :
    Integrable (fun ω => w (Z u ω) * G ω) (E.trajLaw T q)
      ∧ ∫ ω, w (Z u ω) * G ω ∂(E.trajLaw T q)
        = w true * (q (u : ℕ) * ∫ ω, G ω ∂(E.trajLaw T (Function.update q (u : ℕ) 1)))
          + w false
            * ((1 - q (u : ℕ)) * ∫ ω, G ω ∂(E.trajLaw T (Function.update q (u : ℕ) 0))) := by
  have hGi : Integrable G (E.trajLaw T q) := (integral_trajLaw E T q hq G hG hint).1
  have hind : ∀ z : Bool,
      Integrable (fun ω => if Z u ω = z then G ω else 0) (E.trajLaw T q) := by
    intro z
    have hs : MeasurableSet {ω : Traj S T | Z u ω = z} :=
      measurable_Z u (measurableSet_singleton z)
    refine (hGi.indicator hs).congr (Filter.Eventually.of_forall fun ω => ?_)
    show {ω : Traj S T | Z u ω = z}.indicator G ω = if Z u ω = z then G ω else 0
    by_cases h : Z u ω = z
    · rw [Set.indicator_of_mem (by exact h), if_pos h]
    · rw [Set.indicator_of_notMem (by exact h), if_neg h]
  have hdecomp : (fun ω : Traj S T => w (Z u ω) * G ω)
      = fun ω => w true * (if Z u ω = true then G ω else 0)
          + w false * (if Z u ω = false then G ω else 0) := by
    funext ω
    cases h : Z u ω <;> simp
  have hT : ∫ ω, (if Z u ω = true then G ω else 0) ∂(E.trajLaw T q)
      = q (u : ℕ) * ∫ ω, G ω ∂(E.trajLaw T (Function.update q (u : ℕ) 1)) :=
    integral_indicator_Z_mul E T q hq u true G hG hint
  have hF : ∫ ω, (if Z u ω = false then G ω else 0) ∂(E.trajLaw T q)
      = (1 - q (u : ℕ)) * ∫ ω, G ω ∂(E.trajLaw T (Function.update q (u : ℕ) 0)) :=
    integral_indicator_Z_mul E T q hq u false G hG hint
  refine ⟨?_, ?_⟩
  · rw [hdecomp]
    exact ((hind true).const_mul _).add ((hind false).const_mul _)
  · rw [hdecomp, integral_add ((hind true).const_mul _) ((hind false).const_mul _),
      integral_const_mul, integral_const_mul, hT, hF]

/-- **Score identity.** If the action at time `u` is treatment with probability `θ ∈ (0, 1)`,
then weighting by the score of `Z u` turns an expectation into the difference of the
expectations under the laws that force treatment, respectively control, at time `u`. -/
lemma integral_score_mul {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (u : Fin T) (hqu : q (u : ℕ) = θ)
    (G : Traj S T → ℝ) (hG : Measurable G)
    (hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => G (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2)) :
    Integrable (fun ω => score θ (Z u ω) * G ω) (E.trajLaw T q)
      ∧ ∫ ω, score θ (Z u ω) * G ω ∂(E.trajLaw T q)
        = ∫ ω, G ω ∂(E.trajLaw T (Function.update q (u : ℕ) 1))
          - ∫ ω, G ω ∂(E.trajLaw T (Function.update q (u : ℕ) 0)) := by
  have h := integral_weight_mul E T q hq (score θ) u G hG hint
  have h1 : θ ≠ 0 := hθ0.ne'
  have h2 : 1 - θ ≠ 0 := (sub_pos.2 hθ1).ne'
  refine ⟨h.1, ?_⟩
  rw [h.2, hqu]
  show 1 / θ * (θ * _) + -(1 / (1 - θ)) * ((1 - θ) * _) = _
  field_simp
  ring

/-- The state distribution at time `t` does not depend on the treatment probability at time
`t`. -/
lemma stateVec_update {S : Type} [Fintype S] [DecidableEq S] (E : Env S) (q : ℕ → ℝ) (t : ℕ)
    (a : ℝ) : E.stateVec (Function.update q t a) t = E.stateVec q t := by
  unfold Env.stateVec
  congr 2
  refine List.map_congr_left fun s hs => ?_
  rw [Function.update_of_ne (List.mem_range.1 hs).ne]

/-- The mean reward at time `t` is affine in the treatment probability at time `t`. -/
lemma meanReward_update_affine {S : Type} [Fintype S] [DecidableEq S] (E : Env S) (q : ℕ → ℝ)
    (t : ℕ) (θ : ℝ) :
    (1 - θ) * E.meanReward (Function.update q t 1) t
        + θ * E.meanReward (Function.update q t 0) t
      = E.meanReward (Function.update q t (1 - θ)) t := by
  unfold Env.meanReward
  simp only [stateVec_update, Function.update_self, dotProduct]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold Env.rMix
  ring

/-- **Reward-correction identity.** If the action at time `t` is treatment with probability
`θ ∈ (0, 1)`, then the reward at time `t` reweighted by `w_θ(Z_t)` has the mean of the reward at
time `t` when the action at time `t` is treatment with probability `1 - θ`. -/
lemma integral_rcWeight_mul_Y {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (M : ℝ) (hM : E.RewardBound M) (t : Fin T)
    (hqt : q (t : ℕ) = θ) :
    ∫ ω, rcWeight θ (Z t ω) * Y t ω ∂(E.trajLaw T q)
      = E.meanReward (Function.update q (t : ℕ) (1 - θ)) (t : ℕ) := by
  have h := integral_weight_mul E T q hq (rcWeight θ) t (Y t) (measurable_Y t)
    (integrable_Y_path E M hM t)
  have hA : ∫ ω, Y t ω ∂(E.trajLaw T (Function.update q (t : ℕ) 1))
      = E.meanReward (Function.update q (t : ℕ) 1) (t : ℕ) :=
    integral_Y_trajLaw E T _ (update_mem q hq (t : ℕ) 1 ⟨zero_le_one, le_refl _⟩) M hM t
  have hB : ∫ ω, Y t ω ∂(E.trajLaw T (Function.update q (t : ℕ) 0))
      = E.meanReward (Function.update q (t : ℕ) 0) (t : ℕ) :=
    integral_Y_trajLaw E T _ (update_mem q hq (t : ℕ) 0 ⟨le_refl _, zero_le_one⟩) M hM t
  have h1 : θ ≠ 0 := hθ0.ne'
  have h2 : 1 - θ ≠ 0 := (sub_pos.2 hθ1).ne'
  rw [h.2, hqt, hA, hB, ← meanReward_update_affine E q (t : ℕ) θ]
  show (1 - θ) / θ * (θ * _) + θ / (1 - θ) * ((1 - θ) * _) = _
  field_simp

end TPG_B1_rc

open TPG_B1_rc in
theorem solution {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ M : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : E.RewardBound M) :
    ∫ ω, rcEst θ T k ω ∂(E.expLaw T θ)
      = (1 / (T : ℝ)) * ∑ u : Fin T,
          ((E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (u : ℕ)
              - E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (u : ℕ))
            + ∑ t : Fin T,
                if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
                  (E.meanReward
                      (Function.update (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ) (1 - θ)) (t : ℕ)
                    - E.meanReward
                      (Function.update (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ) (1 - θ)) (t : ℕ))
                else 0) := by
  have hq : ∀ s : ℕ, 0 ≤ (fun _ : ℕ => θ) s ∧ (fun _ : ℕ => θ) s ≤ 1 :=
    fun _ => ⟨hθ0.le, hθ1.le⟩
  have hq1 : ∀ (u s : ℕ), 0 ≤ Function.update (fun _ : ℕ => θ) u 1 s
      ∧ Function.update (fun _ : ℕ => θ) u 1 s ≤ 1 :=
    fun u => update_mem _ hq u 1 ⟨zero_le_one, le_refl _⟩
  have hq0 : ∀ (u s : ℕ), 0 ≤ Function.update (fun _ : ℕ => θ) u 0 s
      ∧ Function.update (fun _ : ℕ => θ) u 0 s ≤ 1 :=
    fun u => update_mem _ hq u 0 ⟨le_refl _, zero_le_one⟩
  -- the term `t = u`: `E_θ[s_θ(Z_u) Y_u]`
  have hkey0 : ∀ u : Fin T,
      Integrable (fun ω : Traj S T => score θ (Z u ω) * Y u ω) (E.trajLaw T (fun _ => θ))
      ∧ ∫ ω, score θ (Z u ω) * Y u ω ∂(E.trajLaw T (fun _ => θ))
        = E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (u : ℕ)
          - E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (u : ℕ) := by
    intro u
    have h := integral_score_mul E T (fun _ => θ) hq θ hθ0 hθ1 u rfl (Y u) (measurable_Y u)
      (integrable_Y_path E M hM u)
    refine ⟨h.1, ?_⟩
    rw [h.2, integral_Y_trajLaw E T _ (hq1 (u : ℕ)) M hM u,
      integral_Y_trajLaw E T _ (hq0 (u : ℕ)) M hM u]
    rfl
  -- the terms `u < t`: `E_θ[s_θ(Z_u) w_θ(Z_t) Y_t]`
  have hkey1 : ∀ u t : Fin T, (u : ℕ) < (t : ℕ) →
      Integrable (fun ω : Traj S T => score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω))
        (E.trajLaw T (fun _ => θ))
      ∧ ∫ ω, score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) ∂(E.trajLaw T (fun _ => θ))
        = E.meanReward
            (Function.update (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ) (1 - θ)) (t : ℕ)
          - E.meanReward
            (Function.update (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ) (1 - θ)) (t : ℕ) := by
    intro u t hut
    have hne : (t : ℕ) ≠ (u : ℕ) := hut.ne'
    have hG : Measurable (fun ω : Traj S T => rcWeight θ (Z t ω) * Y t ω) :=
      ((Measurable.of_discrete (f := rcWeight θ)).comp (measurable_Z t)).mul (measurable_Y t)
    have hGint : ∀ p : (Fin T → S) × (Fin T → Bool),
        Integrable (fun y : Fin T → ℝ =>
          (fun ω : Traj S T => rcWeight θ (Z t ω) * Y t ω) (embedPath p.1 p.2 y))
          (E.rewardLaw p.1 p.2) :=
      fun p => (integrable_Y_path E M hM t p).const_mul (rcWeight θ (p.2 t))
    have h := integral_score_mul E T (fun _ => θ) hq θ hθ0 hθ1 u rfl _ hG hGint
    refine ⟨h.1, ?_⟩
    rw [h.2,
      integral_rcWeight_mul_Y E T _ (hq1 (u : ℕ)) θ hθ0 hθ1 M hM t
        (Function.update_of_ne hne _ _),
      integral_rcWeight_mul_Y E T _ (hq0 (u : ℕ)) θ hθ0 hθ1 M hM t
        (Function.update_of_ne hne _ _)]
  have hterm : ∀ u t : Fin T,
      Integrable (fun ω : Traj S T =>
        if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
          score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) else 0)
        (E.trajLaw T (fun _ => θ)) := by
    intro u t
    split_ifs with h
    · exact (hkey1 u t h.1).1
    · exact integrable_zero _ _ _
  have hsum : ∀ u : Fin T,
      Integrable (fun ω : Traj S T => ∑ t : Fin T,
        if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
          score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) else 0)
        (E.trajLaw T (fun _ => θ)) :=
    fun u => integrable_finsetSum Finset.univ (fun t _ => hterm u t)
  have hadd : ∀ u : Fin T,
      Integrable (fun ω : Traj S T => score θ (Z u ω) * Y u ω + ∑ t : Fin T,
        if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
          score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) else 0)
        (E.trajLaw T (fun _ => θ)) :=
    fun u => (hkey0 u).1.add (hsum u)
  -- the estimator as a sum of such terms
  have hrew : ∀ ω : Traj S T, rcEst θ T k ω
      = (1 / (T : ℝ)) * ∑ u : Fin T,
          (score θ (Z u ω) * Y u ω + ∑ t : Fin T,
            if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
              score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) else 0) := by
    intro ω
    unfold rcEst
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_ite, mul_zero]
  have hrew' : ∫ ω, rcEst θ T k ω ∂(E.trajLaw T (fun _ => θ))
      = ∫ ω, ((1 / (T : ℝ)) * ∑ u : Fin T,
          (score θ (Z u ω) * Y u ω + ∑ t : Fin T,
            if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
              score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) else 0))
          ∂(E.trajLaw T (fun _ => θ)) :=
    integral_congr_ae (Filter.Eventually.of_forall hrew)
  show ∫ ω, rcEst θ T k ω ∂(E.trajLaw T (fun _ => θ)) = _
  rw [hrew', integral_const_mul]
  congr 1
  rw [integral_finsetSum Finset.univ (fun u _ => hadd u)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_add (hkey0 u).1 (hsum u), (hkey0 u).2]
  congr 1
  rw [integral_finsetSum Finset.univ (fun t _ => hterm u t)]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with h
  · exact (hkey1 u t h.1).2
  · exact integral_zero _ _
