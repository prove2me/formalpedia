-- Prove2me | solution 2 for StableMSR.Recovery.Supplement.rational_single_run_program
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T06:31:24.383212+00:00
-- url     : https://prove2.me/submissions/20ae861e-09c1-4f73-856a-e3e4fdc7aada

import Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution
import Theorems.Thm_StableMSR_Recovery_rational_recovery_program
import Theorems.Thm_StableMSR_Recovery_validLabels_feasible

set_option autoImplicit false
open scoped Classical ENNReal

namespace StableMSR.Recovery.Supplement

lemma step_tape_irrel (P : MinSumFPT.Program)
    (hP : ∀ i ∈ P, match i with
      | .unif _ | .uniformIndex _ _ => False
      | _ => True) {n : ℕ} (d : Point n → Point n → ℝ) (ω ω' : ℕ → ℝ)
    (s : MinSumFPT.State) : MinSumFPT.step P d ω s = MinSumFPT.step P d ω' s := by
  unfold MinSumFPT.step
  by_cases h : s.halted
  · simp [h]
  · simp only [h]
    cases hi : P[s.cfg.pc]? with
    | none => rfl
    | some i =>
      have hmem : i ∈ P := List.mem_of_getElem? hi
      have := hP i hmem
      cases i <;> simp_all

lemma run_tape_irrel (P : MinSumFPT.Program)
    (hP : ∀ i ∈ P, match i with
      | .unif _ | .uniformIndex _ _ => False
      | _ => True) (n k : ℕ) (d : Point n → Point n → ℝ) (ω : ℕ → ℝ) (t : ℕ) :
    MinSumFPT.run P n k 0 0 d ω t = MinSumFPT.run P n k 0 0 d (fun _ => 0) t := by
  unfold MinSumFPT.run
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact step_tape_irrel P hP d ω _ _

lemma run_halted (P : MinSumFPT.Program) (n k : ℕ) (d : Point n → Point n → ℝ) (ω : ℕ → ℝ)
    (t : ℕ) (h : (MinSumFPT.run P n k 0 0 d ω t).halted = true) (m : ℕ) :
    MinSumFPT.run P n k 0 0 d ω (t + m) = MinSumFPT.run P n k 0 0 d ω t := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have : MinSumFPT.run P n k 0 0 d ω (t + (m + 1)) =
        MinSumFPT.step P d ω (MinSumFPT.run P n k 0 0 d ω (t + m)) := by
      unfold MinSumFPT.run
      rw [← add_assoc, Function.iterate_succ_apply']
    rw [this, ih]
    unfold MinSumFPT.step
    simp [h]

theorem rational_single_run_program_aux :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∀ e : ℚ, 0 < e → e < 1 →
      ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧
        ∀ (n k : ℕ) (d : Point n → Point n → ℝ), 1 ≤ k → k ≤ n → IsMetricArray d →
          let T := a*n^(b*parameterEnvelope (e:ℝ))
          AlwaysFeasible P n k d T ∧ ∀ O : Partition n,
            Stable d k (1+(e:ℝ)) O →
            MinSumFPT.tapeLaw {ω | randomOutput P n k d T ω ≠ O} ≤ (2/3 : ENNReal) := by
  obtain ⟨a, b, ha, hb, H⟩ := StableMSR.Recovery.rational_recovery_program
  refine ⟨a, b, ha, hb, fun e he0 he1 => ?_⟩
  obtain ⟨P, ⟨hadm, hdet⟩, H2⟩ := H e he0 he1
  refine ⟨P, hadm, fun n k d hk hkn hd => ?_⟩
  obtain ⟨t, ht, hs⟩ := H2 n k d hk hkn hd
  simp only at hs ⊢
  obtain ⟨hh, hw, hv, hst⟩ := hs
  have hrun : ∀ ω : Tape, randomState P n k d ω (a*n^(b*parameterEnvelope (e:ℝ))) =
      StableMSR.Recovery.execute P n k d t := by
    intro ω
    unfold randomState StableMSR.Recovery.execute
    rw [run_tape_irrel P hdet n k d ω]
    have hh' : (MinSumFPT.run P n k 0 0 d (fun _ => 0) t).halted = true := hh
    have := run_halted P n k d (fun _ => 0) t hh' (a*n^(b*parameterEnvelope (e:ℝ)) - t)
    rw [Nat.add_sub_cancel' ht] at this
    exact this
  refine ⟨fun ω => ⟨t, ht, ?_⟩, fun O hO => ?_⟩
  · have : randomState P n k d ω t = StableMSR.Recovery.execute P n k d t := by
      unfold randomState StableMSR.Recovery.execute
      rw [run_tape_irrel P hdet n k d ω]
    simp only [this]
    exact ⟨hh, hw, hv, StableMSR.Recovery.validLabels_feasible _ hv⟩
  · have : {ω | randomOutput P n k d (a*n^(b*parameterEnvelope (e:ℝ))) ω ≠ O} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      unfold randomOutput
      rw [hrun ω]
      exact hst O hO
    rw [this]
    simp

end StableMSR.Recovery.Supplement

open StableMSR.Recovery StableMSR.Recovery.Supplement

theorem solution :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∀ e : ℚ, 0 < e → e < 1 →
      ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧
        ∀ (n k : ℕ) (d : Point n → Point n → ℝ), 1 ≤ k → k ≤ n → IsMetricArray d →
          let T := a*n^(b*parameterEnvelope (e:ℝ))
          AlwaysFeasible P n k d T ∧ ∀ O : Partition n,
            Stable d k (1+(e:ℝ)) O →
            MinSumFPT.tapeLaw {ω | randomOutput P n k d T ω ≠ O} ≤ (2/3 : ENNReal) :=
  rational_single_run_program_aux
