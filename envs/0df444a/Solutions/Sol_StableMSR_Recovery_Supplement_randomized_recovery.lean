-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.randomized_recovery
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T01:00:59.593388+00:00
-- url     : https://prove2.me/submissions/ca8777d9-788d-4d19-bed3-c097b82325ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_Supplement_rational_single_run_program
import Theorems.Thm_StableMSR_Recovery_parameterEnvelope_bound
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

/-- A halted interpreter is a fixed point; its partition at the full common
budget is the feasible answer certified at its possibly earlier stopping time. -/
theorem output_feasible_at_budget {n k T : ℕ} (d : Point n → Point n → ℝ) (P : MinSumFPT.Program)
    (always : AlwaysFeasible P n k d T) (ω : Tape) : Feasible Finset.univ k (randomOutput P n k d T ω) := by
  obtain ⟨t,ht,halt,_,_,feas⟩ := always ω
  let step := MinSumFPT.step P d ω
  let s := randomState P n k d ω t
  have fixed : step s = s := by simp only [step,MinSumFPT.step,show s.halted = true from halt,if_true]
  have eq : randomState P n k d ω T = s := by
    change step^[T] _ = s
    rw [show T = (T-t)+t by omega,Function.iterate_add_apply]
    exact Function.iterate_fixed fixed _
  change Feasible Finset.univ k (outputPartition n k (randomState P n k d ω T))
  rw [eq]; exact feas

theorem identity_optimum {n k : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (γ : ℝ)
    (ge : 1 ≤ γ) (O : Partition n) (st : Stable d k γ O) : UniqueOptimal d Finset.univ k O := by
  obtain ⟨m,hm⟩ := hd
  letI := m
  apply st.2 d
  constructor
  · intro x y; rw [←hm x y,←hm y x,dist_comm]
  · intro x y
    exact ⟨le_rfl,by simpa using mul_le_mul_of_nonneg_right ge (hm x y ▸ dist_nonneg (x:=x) (y:=y))⟩

lemma stable_at_lower_factor {n k : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    {lo hi : ℝ} (le : lo ≤ hi) (O : Partition n) (st : Stable d k hi O) : Stable d k lo O := by
  obtain ⟨m,hm⟩ := hd
  letI := m
  refine ⟨st.1,fun d' hp => st.2 d' ⟨hp.1,?_⟩⟩
  intro x y
  refine ⟨(hp.2 x y).1,(hp.2 x y).2.trans (mul_le_mul_of_nonneg_right le ?_)⟩
  rw [←hm x y]; exact dist_nonneg

/-- All tie choices among minimum-cost outputs succeed whenever one run hits
the unique optimum. This uses the public tape law and output definition. -/
theorem tape_failure_power {n k T : ℕ} (d : Point n → Point n → ℝ) (P : MinSumFPT.Program)
    (always : AlwaysFeasible P n k d T) (O : Partition n) (opt : UniqueOptimal d Finset.univ k O)
    (q : ℝ≥0∞) (one : MinSumFPT.tapeLaw {ω | randomOutput P n k d T ω ≠ O} ≤ q) (m : ℕ) :
    independentTapes m {ω | CheapestFailure P n k d T m O ω} ≤ q^m := by
  classical
  let F := {ω | randomOutput P n k d T ω ≠ O}
  have restrictProb : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Icc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ,Real.volume_Icc]; norm_num⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure ((volume : Measure ℝ).restrict (Icc (0:ℝ) 1)) := fun _ => restrictProb
  letI : IsProbabilityMeasure MinSumFPT.tapeLaw :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => (volume : Measure ℝ).restrict (Icc (0:ℝ) 1))))
  have incl : {ω | CheapestFailure P n k d T m O ω} ⊆ Set.univ.pi (fun _ : Fin m => F) := by
    rintro ω ⟨i,low,wrong⟩ j _ hit
    have le := low j
    change randomOutput P n k d T (ω j) = O at hit
    rw [hit] at le
    exact wrong (opt.2 _ ⟨output_feasible_at_budget d P always _,fun B hb => le.trans (opt.1.2 B hb)⟩)
  refine (measure_mono incl).trans ?_
  unfold independentTapes
  rw [Measure.pi_pi]; simpa using pow_le_pow_left' one m

/-- Rational slack absorbs a factor of 32 in the inverse-fifth envelope. -/
theorem choose_slack {K γ : ℝ} (pos : 0 < K) (hγ : 1 < γ ∧ γ < 2)
    (env : ∀ e : ℝ, 0 < e → e < 1 → (parameterEnvelope e : ℝ) ≤ K/e^5) :
    ∃ e : ℚ, 0 < e ∧ e < 1 ∧ (γ-1)/2 ≤ (e : ℝ) ∧ (e:ℝ) < γ-1 ∧
      (parameterEnvelope (e:ℝ):ℝ) ≤ (32*K)/(γ-1)^5 := by
  obtain ⟨e,lo,hi⟩ := exists_rat_btwn (show (γ-1)/2 < γ-1 by linarith [hγ.1])
  have e0 : (0:ℝ) < e := by linarith [hγ.1]
  have e1 : (e:ℝ) < 1 := by linarith [hγ.2]
  refine ⟨e,by exact_mod_cast e0,by exact_mod_cast e1,lo.le,hi,(env _ e0 e1).trans ?_⟩
  have eps : 0 < γ-1 := sub_pos.mpr hγ.1
  have pw := pow_le_pow_left₀ eps.le (show γ-1 ≤ 2*(e:ℝ) by linarith) 5
  rw [div_le_div_iff₀ (pow_pos e0 _) (pow_pos eps _)]
  calc
    K * (γ-1)^5 ≤ K * (2*(e:ℝ))^5 := mul_le_mul_of_nonneg_left pw pos.le
    _ = (32*K)*(e:ℝ)^5 := by ring

end StableMSR.Recovery.Supplement

open StableMSR.Recovery StableMSR.Recovery.Supplement
theorem solution :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → γ < 2 → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1 ∧
        (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5 ∧
        ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            let budget := a * n ^ (b * parameterEnvelope (ε₀ : ℝ))
            AlwaysFeasible P n k d budget ∧
            ∀ O, Stable d k γ O →
              MinSumFPT.tapeLaw {ω | randomOutput P n k d budget ω ≠ O} ≤ (2 / 3 : ENNReal) ∧
              ∀ m : ℕ, 1 ≤ m →
                independentTapes m {ω | CheapestFailure P n k d budget m O ω} ≤
                  (2 / 3 : ENNReal) ^ m := by
  obtain ⟨a,b,ha,hb,machine⟩ := rational_single_run_program
  obtain ⟨K,positive,envelope⟩ := parameterEnvelope_bound
  refine ⟨a,b,ha,hb,32*K,by positivity,?_⟩
  intro γ lower upper
  obtain ⟨e,ep,eu,half,below,power⟩ := choose_slack positive ⟨lower,upper⟩ envelope
  obtain ⟨P,adm,runs⟩ := machine e ep eu
  refine ⟨e,ep,eu,half,below,power,P,adm,?_⟩
  intro n k d hk hn hd
  obtain ⟨feasible,success⟩ := runs n k d hk hn hd
  refine ⟨feasible,?_⟩
  intro O stable
  have weak := stable_at_lower_factor d hd (show 1+(e:ℝ) ≤ γ by linarith) O stable
  have fail := success O weak
  exact ⟨fail,fun m _ => tape_failure_power d P feasible O (identity_optimum d hd γ lower.le O stable) _ fail m⟩
