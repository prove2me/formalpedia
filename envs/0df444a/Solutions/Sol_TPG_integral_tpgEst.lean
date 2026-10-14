-- Prove2me | solution 1 for TPG.integral_tpgEst
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:22:04.120046+00:00
-- url     : https://prove2.me/submissions/68e9d872-950e-4063-bb0e-c1e425923f56

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

namespace TPG_B1_tpg

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
  have hdecomp : (fun ω : Traj S T => score θ (Z u ω) * G ω)
      = fun ω => (1 / θ) * (if Z u ω = true then G ω else 0)
          - (1 / (1 - θ)) * (if Z u ω = false then G ω else 0) := by
    funext ω
    cases h : Z u ω <;> simp [score]
  have hT : ∫ ω, (if Z u ω = true then G ω else 0) ∂(E.trajLaw T q)
      = q (u : ℕ) * ∫ ω, G ω ∂(E.trajLaw T (Function.update q (u : ℕ) 1)) :=
    integral_indicator_Z_mul E T q hq u true G hG hint
  have hF : ∫ ω, (if Z u ω = false then G ω else 0) ∂(E.trajLaw T q)
      = (1 - q (u : ℕ)) * ∫ ω, G ω ∂(E.trajLaw T (Function.update q (u : ℕ) 0)) :=
    integral_indicator_Z_mul E T q hq u false G hG hint
  have h1 : θ ≠ 0 := hθ0.ne'
  have h2 : 1 - θ ≠ 0 := (sub_pos.2 hθ1).ne'
  refine ⟨?_, ?_⟩
  · rw [hdecomp]
    exact ((hind true).const_mul _).sub ((hind false).const_mul _)
  · rw [hdecomp, integral_sub ((hind true).const_mul _) ((hind false).const_mul _),
      integral_const_mul, integral_const_mul, hT, hF, hqu]
    field_simp

end TPG_B1_tpg

open TPG_B1_tpg in
theorem solution {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ M : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : E.RewardBound M) :
    ∫ ω, tpgEst θ T k ω ∂(E.expLaw T θ)
      = (1 / (T : ℝ)) * ∑ u : Fin T, ∑ t : Fin T,
          if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
            (E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ)
              - E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ))
          else 0 := by
  have hq : ∀ s : ℕ, 0 ≤ (fun _ : ℕ => θ) s ∧ (fun _ : ℕ => θ) s ≤ 1 :=
    fun _ => ⟨hθ0.le, hθ1.le⟩
  -- one summand: `E_θ[s_θ(Z_u) Y_t]`
  have hkey : ∀ u t : Fin T,
      Integrable (fun ω : Traj S T => score θ (Z u ω) * Y t ω) (E.trajLaw T (fun _ => θ))
      ∧ ∫ ω, score θ (Z u ω) * Y t ω ∂(E.trajLaw T (fun _ => θ))
        = E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ)
          - E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ) := by
    intro u t
    have h := integral_score_mul E T (fun _ => θ) hq θ hθ0 hθ1 u rfl (Y t) (measurable_Y t)
      (integrable_Y_path E M hM t)
    refine ⟨h.1, ?_⟩
    rw [h.2,
      integral_Y_trajLaw E T _ (update_mem _ hq (u : ℕ) 1 ⟨zero_le_one, le_refl _⟩) M hM t,
      integral_Y_trajLaw E T _ (update_mem _ hq (u : ℕ) 0 ⟨le_refl _, zero_le_one⟩) M hM t]
    rfl
  have hterm : ∀ u t : Fin T,
      Integrable (fun ω : Traj S T =>
        if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then score θ (Z u ω) * Y t ω else 0)
        (E.trajLaw T (fun _ => θ)) := by
    intro u t
    split_ifs
    · exact (hkey u t).1
    · exact integrable_zero _ _ _
  -- the estimator as a double sum
  have hrew : ∀ ω : Traj S T, tpgEst θ T k ω
      = (1 / (T : ℝ)) * ∑ u : Fin T, ∑ t : Fin T,
          if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then score θ (Z u ω) * Y t ω else 0 := by
    intro ω
    unfold tpgEst
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_ite, mul_zero]
  have hrew' : ∫ ω, tpgEst θ T k ω ∂(E.trajLaw T (fun _ => θ))
      = ∫ ω, ((1 / (T : ℝ)) * ∑ u : Fin T, ∑ t : Fin T,
          if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then score θ (Z u ω) * Y t ω else 0)
          ∂(E.trajLaw T (fun _ => θ)) :=
    integral_congr_ae (Filter.Eventually.of_forall hrew)
  show ∫ ω, tpgEst θ T k ω ∂(E.trajLaw T (fun _ => θ)) = _
  rw [hrew', integral_const_mul]
  congr 1
  rw [integral_finsetSum Finset.univ
    (fun u _ => integrable_finsetSum Finset.univ (fun t _ => hterm u t))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_finsetSum Finset.univ (fun t _ => hterm u t)]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with h
  · exact (hkey u t).2
  · exact integral_zero _ _
