-- Prove2me | solution 2 for StableMSR.Recovery.Supplement.randomized_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T12:52:38.345268+00:00
-- url     : https://prove2.me/submissions/6109a7c6-6b56-413e-ab11-b1e45913df5c

import Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution
import Theorems.Thm_StableMSR_Recovery_Supplement_rational_single_run_program
import Theorems.Thm_StableMSR_Recovery_parameterEnvelope_bound

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

lemma run_stable (P : MinSumFPT.Program) (n k : ℕ) (d : Point n → Point n → ℝ) (ω : Tape)
    (t T : ℕ) (hT : t ≤ T) (h : (randomState P n k d ω t).halted = true) :
    randomState P n k d ω T = randomState P n k d ω t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hT
  induction u with
  | zero => rfl
  | succ u ih =>
    have ih := ih (Nat.le_add_right _ _)
    unfold randomState MinSumFPT.run at ih ⊢
    have hs : ∀ s : MinSumFPT.State, s.halted = true → MinSumFPT.step P d ω s = s := by
      intro s hs
      unfold MinSumFPT.step
      simp [hs]
    rw [← add_assoc, Function.iterate_succ_apply', ih]
    exact hs _ h

instance tapeLaw_prob : MeasureTheory.IsProbabilityMeasure MinSumFPT.tapeLaw := by
  have hunif : MeasureTheory.IsProbabilityMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor
    simp
  let := hunif
  unfold MinSumFPT.tapeLaw
  infer_instance

lemma metric_facts (n : ℕ) (d : Point n → Point n → ℝ) (hd : IsMetricArray d) :
    (∀ x y, d x y = d y x) ∧ ∀ x y, 0 ≤ d x y := by
  obtain ⟨m, hm⟩ := hd
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · rw [← hm, ← hm]; exact @dist_comm _ _ x y
  · rw [← hm]; exact @dist_nonneg _ _ x y

lemma stable_mono (n k : ℕ) (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (γ γ' : ℝ) (h : γ' ≤ γ) (O : Partition n) (hO : Stable d k γ O) : Stable d k γ' O := by
  have hnn := (metric_facts n d hd).2
  exact ⟨hO.1, fun d' hd' => hO.2 d' ⟨hd'.1, fun x y => ⟨(hd'.2 x y).1,
    (hd'.2 x y).2.trans (mul_le_mul_of_nonneg_right h (hnn x y))⟩⟩⟩

end StableMSR.Recovery.Supplement

open StableMSR.Recovery StableMSR.Recovery.Supplement in
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
  obtain ⟨a, b, ha, hb, H⟩ := rational_single_run_program
  obtain ⟨K, hK, hKb⟩ := parameterEnvelope_bound
  refine ⟨a, b, ha, hb, 32 * K, by positivity, fun γ h1 h2 => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (γ - 1) / 2 < γ - 1 by linarith)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1' : (q : ℝ) < 1 := by linarith
  obtain ⟨P, hP, HP⟩ := H q (by exact_mod_cast hq0) (by exact_mod_cast hq1')
  refine ⟨q, by exact_mod_cast hq0, by exact_mod_cast hq1', hq1.le, hq2, ?_, P, hP, ?_⟩
  · refine (hKb q hq0 hq1').trans ?_
    have hpos : 0 < (γ - 1) := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (γ - 1) ^ 5 ≤ 32 * (q : ℝ) ^ 5 := by
      have : (γ - 1) ^ 5 ≤ (2 * (q : ℝ)) ^ 5 := pow_le_pow_left₀ hpos.le (by linarith) 5
      calc _ ≤ _ := this
        _ = _ := by ring
    nlinarith [hK]
  · intro n k d hk hkn hd
    intro budget
    obtain ⟨hF, hS⟩ := HP n k d hk hkn hd
    refine ⟨hF, fun O hO => ?_⟩
    have hO' := stable_mono n k d hd γ (1 + (q : ℝ)) (by linarith) O hO
    have h1 := hS O hO'
    refine ⟨h1, fun m hm => ?_⟩
    obtain ⟨hsym, hnn⟩ := metric_facts n d hd
    have hopt : UniqueOptimal d Finset.univ k O :=
      hO.2 d ⟨hsym, fun x y => ⟨le_rfl, by nlinarith [hnn x y]⟩⟩
    have feas : ∀ x : Tape, Feasible Finset.univ k (randomOutput P n k d budget x) := by
      intro x
      obtain ⟨t, ht, hh, -, -, hfe⟩ := hF x
      have := run_stable P n k d x t budget ht hh
      unfold randomOutput
      rw [this]; exact hfe
    have hsub : {ω : Fin m → Tape | CheapestFailure P n k d budget m O ω} ⊆
        Set.pi Set.univ (fun _ => {ω : Tape | randomOutput P n k d budget ω ≠ O}) := by
      rintro ω ⟨i, hi, hne⟩ j _ heq
      apply hne
      have hij := hi j
      rw [heq] at hij
      refine hopt.2 _ ⟨feas _, fun Q hQ => hij.trans (hopt.1.2 Q hQ)⟩
    calc independentTapes m {ω | CheapestFailure P n k d budget m O ω}
        ≤ independentTapes m (Set.pi Set.univ (fun _ => {ω : Tape | randomOutput P n k d budget ω ≠ O})) :=
          MeasureTheory.measure_mono hsub
      _ = ∏ _ : Fin m, MinSumFPT.tapeLaw {ω : Tape | randomOutput P n k d budget ω ≠ O} :=
          MeasureTheory.Measure.pi_pi _ _
      _ ≤ ∏ _ : Fin m, (2 / 3 : ENNReal) := Finset.prod_le_prod' (fun _ _ => h1)
      _ = (2 / 3 : ENNReal) ^ m := by simp
