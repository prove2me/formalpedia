-- Prove2me | solution 1 for TPG.integral_head_mul_gap_tail
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:26:07.916007+00:00
-- url     : https://prove2.me/submissions/c6415c69-522d-40f9-85ad-a23b15215a16

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge
import Theorems.Thm_TPG_integral_head_mul_tail
import Theorems.Thm_TPG_integral_fun_state_action

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-! ### State distribution of a restarted environment -/

/-- One more step of the state distribution: `μ_{t+1} = μ_t P_{q_t}^t`. -/
private lemma gt_stateVec_succ {S : Type} [Fintype S] [DecidableEq S] (E : Env S) (q : ℕ → ℝ)
    (t : ℕ) : E.stateVec q (t + 1) = Matrix.vecMul (E.stateVec q t) (E.PMix (q t) t) := by
  simp [Env.stateVec, List.range_succ, Matrix.vecMul_vecMul]

/-- The state distribution at time `h` of the environment restarted at time `k` from the state
`a` is the row `a` of the product of the mixed kernels of times `k, …, k + h - 1`. -/
private lemma gt_stateVec_shift {S : Type} [Fintype S] [DecidableEq S] (E : Env S) (k : ℕ)
    (a : S) (q : ℕ → ℝ) (h : ℕ) (b : S) :
    (E.shift k a).stateVec (fun t => q (k + t)) h b
      = ((List.Ico k (k + h)).map (fun s => E.PMix (q s) s)).prod a b := by
  have hI : List.Ico k (k + h) = (List.range h).map (k + ·) := by
    rw [List.Ico, Nat.add_sub_cancel_left, List.range'_eq_map_range]
  have hρ : (E.shift k a).ρ = Pi.single a 1 := by
    funext x
    simp [Env.shift, Pi.single_apply]
  have hP : ∀ (θ : ℝ) (s : ℕ), (E.shift k a).PMix θ s = E.PMix θ (k + s) := fun _ _ => rfl
  rw [hI, List.map_map]
  unfold Env.stateVec
  rw [hρ, Matrix.single_one_vecMul]
  simp only [hP]
  rfl

/-! ### Skipping the first `h + 1` steps -/

/-- Law of the trajectory after the first `h + 1` steps: a mixture over the state at time
`h + 1` of the restarted laws. -/
private lemma gt_tail_succ {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (E : Env S) (h n : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (G : Traj S n → ℝ) (hG : Measurable G) (CG : ℝ) (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, G (tailTraj (h + 1) n ω) ∂(E.trajLaw (h + 1 + n) q)
      = ∑ b : S, E.stateVec q (h + 1) b
          * ∫ ω, G ω ∂((E.shift (h + 1) b).trajLaw n (fun t => q (h + 1 + t))) := by
  have key := integral_head_mul_tail E h n q hq (fun _ => 1) G measurable_const hG 1 CG
    (fun _ => by simp) hGb
  simp only [one_mul] at key
  rw [key]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  have h2 := integral_fun_state_action E (h + 1) q hq (Fin.last h) (fun x z => E.P h z x b)
  simp only [Fin.val_last] at h2
  rw [h2, gt_stateVec_succ]
  simp [Matrix.vecMul, dotProduct, Env.PMix, Matrix.add_apply, Matrix.smul_apply]

/-- Re-indexing a trajectory law along an equality of horizons. -/
private lemma gt_cast {S : Type} [Fintype S] [MeasurableSpace S] (E : Env S) (q : ℕ → ℝ)
    (n : ℕ) (G : Traj S n → ℝ) (N : ℕ) (hN : n = N) :
    ∫ ω : Traj S N, G (fun j => ω (Fin.cast hN j)) ∂(E.trajLaw N q)
      = ∫ ω, G ω ∂(E.trajLaw n q) := by
  subst hN
  rfl

/-- Law of the trajectory restarted at time `k` from `a`, after skipping `h` further steps. -/
private lemma gt_gap {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (E : Env S) (k h n : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (a : S)
    (G : Traj S n → ℝ) (hG : Measurable G) (CG : ℝ) (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, G (tailTraj h n ω) ∂((E.shift k a).trajLaw (h + n) (fun t => q (k + t)))
      = ∑ b : S, ((List.Ico k (k + h)).map (fun s => E.PMix (q s) s)).prod a b
          * ∫ ω, G ω ∂((E.shift (k + h) b).trajLaw n (fun t => q (k + h + t))) := by
  cases h with
  | zero =>
    have h0 : ∀ ω : Traj S (0 + n),
        tailTraj 0 n ω = fun j => ω (Fin.cast (Nat.zero_add n).symm j) := by
      intro ω
      funext j
      simp [tailTraj]
    simp only [h0, Nat.add_zero, List.Ico.self_empty, List.map_nil, List.prod_nil,
      Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact gt_cast (E.shift k a) (fun t => q (k + t)) n G (0 + n) (Nat.zero_add n).symm
  | succ h' =>
    rw [gt_tail_succ (E.shift k a) h' n (fun t => q (k + t)) (fun t => hq _) G hG CG hGb]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gt_stateVec_shift]
    have hE : (E.shift k a).shift (h' + 1) b = E.shift (k + (h' + 1)) b := by
      simp only [Env.shift, Nat.add_assoc]
    have hqq : (fun t => q (k + (h' + 1 + t))) = fun t => q (k + (h' + 1) + t) := by
      funext t
      simp only [Nat.add_assoc]
    rw [hE, hqq]

/-! ### The Markov property across a gap -/

theorem solution {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (m h n : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S (m + 1) → ℝ) (G : Traj S n → ℝ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, F (headTraj (m + 1) (h + n) ω) * G (tailTraj h n (tailTraj (m + 1) (h + n) ω))
        ∂(E.trajLaw (m + 1 + (h + n)) q)
      = ∑ a : S, ∑ b : S,
          (∫ ω, F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a ∂(E.trajLaw (m + 1) q))
            * (((List.Ico (m + 1) (m + 1 + h)).map (fun s => E.PMix (q s) s)).prod a b)
            * ∫ ω, G ω ∂((E.shift (m + 1 + h) b).trajLaw n (fun t => q (m + 1 + h + t))) := by
  have htail : Measurable (tailTraj (S := S) h n) := by
    unfold tailTraj
    exact measurable_pi_lambda _ fun i => measurable_pi_apply _
  rw [integral_head_mul_tail E m (h + n) q hq F (fun ω' => G (tailTraj h n ω')) hF
    (hG.comp htail) CF CG hFb (fun _ => hGb _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [gt_gap E (m + 1) h n q hq a G hG CG hGb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
