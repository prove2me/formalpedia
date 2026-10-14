-- Prove2me | solution 1 for TPG.integral_cond_Z
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:20:55.371992+00:00
-- url     : https://prove2.me/submissions/e069d2c0-b8ee-49b4-8b91-981a319db4e8

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw
import Theorems.Thm_TPG_integral_indicator_Z_mul

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (u : Fin T) (z : Bool) (hu : 0 < q (u : ℕ) ∧ q (u : ℕ) < 1)
    (F : Traj S T → ℝ) (hF : Measurable F)
    (hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => F (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2)) :
    ∫ ω, F ω ∂(ProbabilityTheory.cond (E.trajLaw T q) {ω | Z u ω = z})
      = ∫ ω, F ω ∂(E.trajLaw T (Function.update q (u : ℕ) (if z then 1 else 0))) := by
  -- the updated sequence still takes values in `[0, 1]`, so its law is a probability measure
  have hq' : ∀ t : ℕ, 0 ≤ Function.update q (u : ℕ) (if z then 1 else 0) t
      ∧ Function.update q (u : ℕ) (if z then 1 else 0) t ≤ 1 := by
    intro t
    by_cases h : t = (u : ℕ)
    · subst h
      rw [Function.update_self]
      cases z <;> simp
    · rw [Function.update_of_ne h]
      exact hq t
  have : IsProbabilityMeasure
      (E.trajLaw T (Function.update q (u : ℕ) (if z then 1 else 0))) :=
    isProbabilityMeasure_trajLaw E T _ hq'
  -- the conditioning event is measurable
  have hZ : Measurable (Z u : Traj S T → Bool) := by
    unfold Z
    exact (measurable_pi_apply u).snd.fst
  have hs : MeasurableSet {ω : Traj S T | Z u ω = z} := hZ (measurableSet_singleton z)
  -- its probability is nonzero
  have hc : (if z then q (u : ℕ) else 1 - q (u : ℕ)) ≠ 0 := by
    cases z
    · simpa using (sub_pos.2 hu.2).ne'
    · simpa using hu.1.ne'
  have hind : ∀ G : Traj S T → ℝ,
      ({ω : Traj S T | Z u ω = z}).indicator G = fun ω => if Z u ω = z then G ω else 0 := by
    intro G
    funext ω
    by_cases h : Z u ω = z
    · rw [Set.indicator_of_mem (by exact h), if_pos h]
    · rw [Set.indicator_of_notMem (by exact h), if_neg h]
  -- the probability of the event `{Z u = z}`
  have hconst : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => (fun _ : Traj S T => (1 : ℝ)) (embedPath p.1 p.2 y))
        (E.rewardLaw p.1 p.2) := by
    intro p
    have : IsProbabilityMeasure (E.rewardLaw p.1 p.2) := by
      unfold Env.rewardLaw; infer_instance
    exact integrable_const _
  have h1 : (E.trajLaw T q).real {ω : Traj S T | Z u ω = z}
      = (if z then q (u : ℕ) else 1 - q (u : ℕ)) := by
    rw [← integral_indicator_one hs]
    have h := integral_indicator_Z_mul E T q hq u z (fun _ => (1 : ℝ)) measurable_const hconst
    rw [integral_const, probReal_univ, smul_eq_mul, mul_one, mul_one] at h
    rw [← h]
    congr 1
    exact hind 1
  -- assemble
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, ← integral_indicator hs, hind F,
    integral_indicator_Z_mul E T q hq u z F hF hint, ENNReal.toReal_inv, ← measureReal_def, h1,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
