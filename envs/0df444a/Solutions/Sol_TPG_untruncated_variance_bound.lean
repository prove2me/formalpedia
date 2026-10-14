-- Prove2me | solution 1 for TPG.untruncated_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:19:39.905659+00:00
-- url     : https://prove2.me/submissions/6795db55-8fb6-4ac3-b442-8c74fc796f1f

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Estimators
import Theorems.Thm_TPG_integral_trajLaw
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw
import Theorems.Thm_TPG_ae_abs_Y_le
import Theorems.Thm_TPG_integral_indicator_Z_mul

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-- The reward coordinate of a trajectory is measurable. -/
private lemma TPG_measurable_Y {S : Type} [MeasurableSpace S] {T : ℕ} (t : Fin T) :
    Measurable (Y t : Traj S T → ℝ) := by
  unfold Y
  exact (measurable_pi_apply t).snd.snd

/-- The action coordinate of a trajectory is measurable. -/
private lemma TPG_measurable_Z {S : Type} [MeasurableSpace S] {T : ℕ} (t : Fin T) :
    Measurable (Z t : Traj S T → Bool) := by
  unfold Z
  exact (measurable_pi_apply t).snd.fst

/-- The reward law along a fixed path is a probability measure. -/
private lemma TPG_rewardLaw_prob {S : Type} [Fintype S] (E : Env S) {T : ℕ}
    (x : Fin T → S) (z : Fin T → Bool) : IsProbabilityMeasure (E.rewardLaw x z) := by
  unfold Env.rewardLaw
  infer_instance

/-- Overwriting one entry of a `[0,1]`-valued sequence by `0` or `1` keeps it `[0,1]`-valued. -/
private lemma TPG_update_mem {q : ℕ → ℝ} (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (n : ℕ) (z : Bool) :
    ∀ t : ℕ, 0 ≤ Function.update q n (if z then (1 : ℝ) else 0) t
      ∧ Function.update q n (if z then (1 : ℝ) else 0) t ≤ 1 := by
  intro t
  by_cases h : t = n
  · subst h
    cases z <;> simp
  · rw [Function.update_of_ne h]
    exact hq t

/-- **Law of one action.** Under `trajLaw T q` the action at time `v` is treatment with
probability `q v`: `E_q[h(Z_v)] = q_v h(1) + (1 - q_v) h(0)`. -/
theorem TPG_integral_fun_Z {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (E : Env S) (T : ℕ) (q : ℕ → ℝ)
    (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (v : Fin T) (h : Bool → ℝ) :
    ∫ ω, h (Z v ω) ∂(E.trajLaw T q)
      = q (v : ℕ) * h true + (1 - q (v : ℕ)) * h false := by
  have hind : ∀ b : Bool, ∫ ω, (if Z v ω = b then h b else 0) ∂(E.trajLaw T q)
      = (if b then q (v : ℕ) else 1 - q (v : ℕ)) * h b := by
    intro b
    have := isProbabilityMeasure_trajLaw E T _ (TPG_update_mem hq (v : ℕ) b)
    rw [integral_indicator_Z_mul E T q hq v b (fun _ => h b) measurable_const (fun p => by
      have := TPG_rewardLaw_prob E p.1 p.2
      exact integrable_const _)]
    rw [integral_const, probReal_univ, one_smul]
  have hsplit : ∀ ω : Traj S T, h (Z v ω)
      = (if Z v ω = true then h true else 0) + (if Z v ω = false then h false else 0) := by
    intro ω
    cases Z v ω <;> simp
  have hmeas : ∀ b : Bool, Measurable (fun ω : Traj S T => if Z v ω = b then h b else 0) :=
    fun b => (Measurable.of_discrete (f := fun z : Bool => if z = b then h b else 0)).comp
      (TPG_measurable_Z v)
  have hI : ∀ b : Bool,
      Integrable (fun ω : Traj S T => if Z v ω = b then h b else 0) (E.trajLaw T q) :=
    fun b => (integral_trajLaw E T q hq _ (hmeas b) (fun p => by
      have := TPG_rewardLaw_prob E p.1 p.2
      show Integrable (fun _ : Fin T → ℝ => if p.2 v = b then h b else 0) _
      exact integrable_const _)).1
  simp_rw [hsplit]
  rw [integral_add (hI true) (hI false), hind true, hind false]
  simp

/-- **Joint law of two actions.** Under `trajLaw T q` the actions at two distinct times are
independent Bernoulli variables:
`E_q[g(Z_u) h(Z_v)] = (q_u g(1) + (1 - q_u) g(0)) (q_v h(1) + (1 - q_v) h(0))` for `u ≠ v`. -/
theorem TPG_integral_fun_Z_mul_fun_Z {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (E : Env S) (T : ℕ) (q : ℕ → ℝ)
    (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (u v : Fin T) (huv : u ≠ v) (g h : Bool → ℝ) :
    ∫ ω, g (Z u ω) * h (Z v ω) ∂(E.trajLaw T q)
      = (q (u : ℕ) * g true + (1 - q (u : ℕ)) * g false)
        * (q (v : ℕ) * h true + (1 - q (v : ℕ)) * h false) := by
  have hne : (v : ℕ) ≠ (u : ℕ) := fun e => huv (Fin.ext e.symm)
  have hmeasF : ∀ a : Bool, Measurable (fun ω : Traj S T => g a * h (Z v ω)) :=
    fun a => (Measurable.of_discrete (f := fun z : Bool => g a * h z)).comp (TPG_measurable_Z v)
  have hind : ∀ a : Bool,
      ∫ ω, (if Z u ω = a then g a * h (Z v ω) else 0) ∂(E.trajLaw T q)
        = (if a then q (u : ℕ) else 1 - q (u : ℕ))
          * (g a * (q (v : ℕ) * h true + (1 - q (v : ℕ)) * h false)) := by
    intro a
    have hq' := TPG_update_mem hq (u : ℕ) a
    rw [integral_indicator_Z_mul E T q hq u a (fun ω => g a * h (Z v ω)) (hmeasF a) (fun p => by
      have := TPG_rewardLaw_prob E p.1 p.2
      show Integrable (fun _ : Fin T → ℝ => g a * h (p.2 v)) _
      exact integrable_const _)]
    rw [integral_const_mul, TPG_integral_fun_Z E T _ hq' v h, Function.update_of_ne hne]
  have hsplit : ∀ ω : Traj S T, g (Z u ω) * h (Z v ω)
      = (if Z u ω = true then g true * h (Z v ω) else 0)
        + (if Z u ω = false then g false * h (Z v ω) else 0) := by
    intro ω
    cases Z u ω <;> simp
  have hmeas : ∀ a : Bool,
      Measurable (fun ω : Traj S T => if Z u ω = a then g a * h (Z v ω) else 0) :=
    fun a => (Measurable.of_discrete
      (f := fun p : Bool × Bool => if p.1 = a then g a * h p.2 else 0)).comp
        ((TPG_measurable_Z u).prodMk (TPG_measurable_Z v))
  have hI : ∀ a : Bool,
      Integrable (fun ω : Traj S T => if Z u ω = a then g a * h (Z v ω) else 0)
        (E.trajLaw T q) :=
    fun a => (integral_trajLaw E T q hq _ (hmeas a) (fun p => by
      have := TPG_rewardLaw_prob E p.1 p.2
      show Integrable (fun _ : Fin T → ℝ => if p.2 u = a then g a * h (p.2 v) else 0) _
      exact integrable_const _)).1
  simp_rw [hsplit]
  rw [integral_add (hI true) (hI false), hind true, hind false]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

/-- Second moments of the scores at `θ = 1/2`: `E[s_u s_v] = 4 · 1{u = v}`. -/
private lemma TPG_integral_score_mul_score {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (E : Env S) (T : ℕ) (u v : Fin T) :
    ∫ ω, score (1 / 2) (Z u ω) * score (1 / 2) (Z v ω) ∂(E.trajLaw T (fun _ => (1 / 2 : ℝ)))
      = if u = v then 4 else 0 := by
  have hq : ∀ t : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => (1 / 2 : ℝ)) t ∧ (fun _ : ℕ => (1 / 2 : ℝ)) t ≤ 1 :=
    fun _ => by norm_num
  by_cases huv : u = v
  · subst huv
    have := isProbabilityMeasure_trajLaw E T _ hq
    have h4 : ∀ z : Bool, score (1 / 2) z * score (1 / 2) z = 4 := by
      intro z
      cases z <;> norm_num [score]
    simp_rw [h4]
    rw [integral_const, probReal_univ, one_smul]
    simp
  · rw [TPG_integral_fun_Z_mul_fun_Z E T _ hq u v huv, if_neg huv]
    norm_num [score]

/-- The product of two scores is integrable. -/
private lemma TPG_integrable_score_mul_score {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (E : Env S) (T : ℕ) (u v : Fin T) :
    Integrable (fun ω : Traj S T => score (1 / 2) (Z u ω) * score (1 / 2) (Z v ω))
      (E.trajLaw T (fun _ => (1 / 2 : ℝ))) := by
  have hq : ∀ t : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => (1 / 2 : ℝ)) t ∧ (fun _ : ℕ => (1 / 2 : ℝ)) t ≤ 1 :=
    fun _ => by norm_num
  have hmeas : Measurable
      (fun ω : Traj S T => score (1 / 2) (Z u ω) * score (1 / 2) (Z v ω)) :=
    (Measurable.of_discrete
      (f := fun p : Bool × Bool => score (1 / 2) p.1 * score (1 / 2) p.2)).comp
        ((TPG_measurable_Z u).prodMk (TPG_measurable_Z v))
  exact (integral_trajLaw E T _ hq _ hmeas (fun p => by
    have := TPG_rewardLaw_prob E p.1 p.2
    show Integrable (fun _ : Fin T → ℝ => score (1 / 2) (p.2 u) * score (1 / 2) (p.2 v)) _
    exact integrable_const _)).1

/-- Second moment of a partial sum of scores: `E[(∑_{u ∈ A} s_u)²] = 4 |A|`. -/
private lemma TPG_integral_sq_sum_score {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (E : Env S) (T : ℕ) (A : Finset (Fin T)) :
    Integrable (fun ω : Traj S T => (∑ u ∈ A, score (1 / 2) (Z u ω)) ^ 2)
        (E.trajLaw T (fun _ => (1 / 2 : ℝ)))
      ∧ ∫ ω, (∑ u ∈ A, score (1 / 2) (Z u ω)) ^ 2 ∂(E.trajLaw T (fun _ => (1 / 2 : ℝ)))
        = 4 * (A.card : ℝ) := by
  have hexp : ∀ ω : Traj S T, (∑ u ∈ A, score (1 / 2) (Z u ω)) ^ 2
      = ∑ u ∈ A, ∑ v ∈ A, score (1 / 2) (Z u ω) * score (1 / 2) (Z v ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  have hI : ∀ u ∈ A, Integrable
      (fun ω : Traj S T => ∑ v ∈ A, score (1 / 2) (Z u ω) * score (1 / 2) (Z v ω))
      (E.trajLaw T (fun _ => (1 / 2 : ℝ))) :=
    fun u _ => integrable_finsetSum _ fun v _ => TPG_integrable_score_mul_score E T u v
  refine ⟨integrable_finsetSum _ hI, ?_⟩
  rw [integral_finsetSum _ hI]
  have hinner : ∀ u ∈ A,
      ∫ ω, ∑ v ∈ A, score (1 / 2) (Z u ω) * score (1 / 2) (Z v ω)
        ∂(E.trajLaw T (fun _ => (1 / 2 : ℝ))) = 4 := by
    intro u hu
    rw [integral_finsetSum _ fun v _ => TPG_integrable_score_mul_score E T u v]
    simp_rw [TPG_integral_score_mul_score]
    rw [Finset.sum_ite_eq, if_pos hu]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Reversing the order of summation in the untruncated estimator:
`tpgEst (1/2) T T = (1/T) ∑_t Y_t ∑_{u ≤ t} s_u`. -/
private lemma TPG_tpgEst_reorder {S : Type} [Fintype S] (T : ℕ) (ω : Traj S T) :
    tpgEst (1 / 2) T T ω
      = (1 / (T : ℝ)) * ∑ t : Fin T, Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω) := by
  unfold tpgEst
  congr 1
  have h1 : ∀ u : Fin T, score (1 / 2) (Z u ω) *
      ∑ t : Fin T, (if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + T then Y t ω else 0)
      = ∑ t : Fin T, if u ∈ Finset.Iic t then Y t ω * score (1 / 2) (Z u ω) else 0 := by
    intro u
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : u ≤ t
    · have h' : (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + T :=
        ⟨Fin.le_def.1 h, by have := t.isLt; omega⟩
      rw [if_pos h', if_pos (Finset.mem_Iic.2 h)]
      ring
    · have h' : ¬ ((u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + T) :=
        fun hh => h (Fin.le_def.2 hh.1)
      rw [if_neg h', if_neg (fun hh => h (Finset.mem_Iic.1 hh))]
      ring
  rw [Finset.sum_congr rfl fun u _ => h1 u]
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]

/-- `∑_{t < T} (t + 1) = T (T + 1) / 2`. -/
private lemma TPG_sum_fin_succ (T : ℕ) :
    ∑ t : Fin T, (((t : ℕ) : ℝ) + 1) = (T : ℝ) * ((T : ℝ) + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1)) T]
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (M : ℝ) (hT : 0 < T) (hM : E.RewardBound M) :
    variance (tpgEst (1 / 2) T T) (E.expLaw T (1 / 2)) ≤ 2 * M ^ 2 * ((T : ℝ) + 1) := by
  have hq : ∀ t : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => (1 / 2 : ℝ)) t ∧ (fun _ : ℕ => (1 / 2 : ℝ)) t ≤ 1 :=
    fun _ => by norm_num
  have hprob : IsProbabilityMeasure (E.trajLaw T (fun _ => (1 / 2 : ℝ))) :=
    isProbabilityMeasure_trajLaw E T _ hq
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.2 hT
  unfold Env.expLaw
  -- the dominating function
  have hGint : Integrable (fun ω : Traj S T => (1 / (T : ℝ)) *
      ∑ t : Fin T, M ^ 2 * (∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2)
      (E.trajLaw T (fun _ => (1 / 2 : ℝ))) :=
    (integrable_finsetSum _ fun t _ =>
      ((TPG_integral_sq_sum_score E T (Finset.Iic t)).1).const_mul (M ^ 2)).const_mul _
  have hGval : ∫ ω, (1 / (T : ℝ)) *
      ∑ t : Fin T, M ^ 2 * (∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2
        ∂(E.trajLaw T (fun _ => (1 / 2 : ℝ))) = 2 * M ^ 2 * ((T : ℝ) + 1) := by
    rw [integral_const_mul, integral_finsetSum _ fun t _ =>
      ((TPG_integral_sq_sum_score E T (Finset.Iic t)).1).const_mul (M ^ 2)]
    simp_rw [integral_const_mul, (TPG_integral_sq_sum_score E T _).2, Fin.card_Iic]
    have hsum : ∑ t : Fin T, M ^ 2 * (4 * (((t : ℕ) + 1 : ℕ) : ℝ))
        = 4 * M ^ 2 * ∑ t : Fin T, (((t : ℕ) : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      push_cast
      ring
    rw [hsum, TPG_sum_fin_succ]
    field_simp
    ring
  have hmeasX : Measurable (tpgEst (1 / 2) T T : Traj S T → ℝ) := by
    unfold tpgEst
    refine measurable_const.mul (Finset.measurable_sum _ fun u _ => ?_)
    refine ((Measurable.of_discrete (f := score (1 / 2))).comp (TPG_measurable_Z u)).mul
      (Finset.measurable_sum _ fun t _ => ?_)
    exact Measurable.ite (MeasurableSet.const _) (TPG_measurable_Y t) measurable_const
  have hle : ∀ᵐ ω ∂(E.trajLaw T (fun _ => (1 / 2 : ℝ))),
      (tpgEst (1 / 2) T T ^ 2) ω ≤ (1 / (T : ℝ)) *
        ∑ t : Fin T, M ^ 2 * (∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2 := by
    filter_upwards [ae_abs_Y_le E T (fun _ => (1 / 2 : ℝ)) M hM] with ω hω
    rw [Pi.pow_apply, TPG_tpgEst_reorder]
    have hcs : (∑ t : Fin T, Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2
        ≤ (T : ℝ) * ∑ t : Fin T, (Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin T)))
        (f := fun t => Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω))
      simpa using this
    have hterm : ∀ t : Fin T, (Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2
        ≤ M ^ 2 * (∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2 := by
      intro t
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (sq_le_sq' (abs_le.1 (hω t)).1 (abs_le.1 (hω t)).2) (sq_nonneg _)
    calc ((1 / (T : ℝ)) * ∑ t : Fin T, Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2
        = (1 / (T : ℝ)) ^ 2
          * (∑ t : Fin T, Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2 := by ring
      _ ≤ (1 / (T : ℝ)) ^ 2 * ((T : ℝ)
          * ∑ t : Fin T, (Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = (1 / (T : ℝ))
          * ∑ t : Fin T, (Y t ω * ∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2 := by
        field_simp
      _ ≤ (1 / (T : ℝ))
          * ∑ t : Fin T, M ^ 2 * (∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => hterm t) (by positivity)
  calc variance (tpgEst (1 / 2) T T) (E.trajLaw T (fun _ => (1 / 2 : ℝ)))
      ≤ ∫ ω, (tpgEst (1 / 2) T T ^ 2) ω ∂(E.trajLaw T (fun _ => (1 / 2 : ℝ))) :=
        variance_le_expectation_sq hmeasX.aestronglyMeasurable
    _ ≤ ∫ ω, (1 / (T : ℝ)) *
          ∑ t : Fin T, M ^ 2 * (∑ u ∈ Finset.Iic t, score (1 / 2) (Z u ω)) ^ 2
            ∂(E.trajLaw T (fun _ => (1 / 2 : ℝ))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hGint hle
    _ = 2 * M ^ 2 * ((T : ℝ) + 1) := hGval
