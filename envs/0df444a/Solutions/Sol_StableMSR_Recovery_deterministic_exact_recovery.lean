-- Prove2me | solution 1 for StableMSR.Recovery.deterministic_exact_recovery
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:32:49.1522+00:00
-- url     : https://prove2.me/submissions/3f27d934-a459-4c23-8273-dbd6fb426c19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_parameterEnvelope_bound
import Theorems.Thm_StableMSR_Recovery_validLabels_feasible
import Theorems.Thm_StableMSR_Recovery_rational_recovery_program


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery
namespace CalibrationAux

/-- A fixed rational stability margin can be selected before the input instance. -/
lemma exists_rational_calibration (γ : ℝ) (hγ : 1 < γ) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
      (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
       else ε₀ = 1 / 2) ∧ 1 + (ε₀ : ℝ) < γ := by
  by_cases hsmall : γ < 2
  · obtain ⟨ε₀, hlo, hhi⟩ :=
      exists_rat_btwn (show (γ - 1) / 2 < γ - 1 by linarith)
    have hpos : (0 : ℝ) < (ε₀ : ℝ) := by linarith
    have hone : (ε₀ : ℝ) < 1 := by linarith
    refine ⟨ε₀, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hpos
    · exact_mod_cast hone
    · simpa only [if_pos hsmall] using And.intro hlo.le hhi
    · linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩
    · simp only [if_neg hsmall]
    · push_cast
      linarith

/-- A fifth-power envelope survives the rational calibration, with an absolute factor 32. -/
lemma exists_calibration_with_envelope (K : ℝ) (hK : 0 < K)
    (hE : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (parameterEnvelope ε : ℝ) ≤ K / ε ^ 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 1 < γ →
      ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        (γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5) ∧
        1 + (ε₀ : ℝ) < γ := by
  refine ⟨32 * K, by positivity, ?_⟩
  intro γ hγ
  obtain ⟨ε₀, hpos, hone, hrange, hmargin⟩ := exists_rational_calibration γ hγ
  refine ⟨ε₀, hpos, hone, hrange, ?_, hmargin⟩
  intro hsmall
  have hepos : (0 : ℝ) < (ε₀ : ℝ) := by exact_mod_cast hpos
  have heone : (ε₀ : ℝ) < 1 := by exact_mod_cast hone
  have hlo : (γ - 1) / 2 ≤ (ε₀ : ℝ) :=
    (by simpa only [if_pos hsmall] using hrange :
      (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1).1
  have hδ : 0 < γ - 1 := by linarith
  have hp : (γ - 1) ^ 5 ≤ (2 * (ε₀ : ℝ)) ^ 5 :=
    pow_le_pow_left₀ hδ.le (by linarith) 5
  rw [mul_pow] at hp
  norm_num at hp
  calc
    (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ K / (ε₀ : ℝ) ^ 5 := hE _ hepos heone
    _ ≤ (32 * K) / (γ - 1) ^ 5 := by
      apply (div_le_div_iff₀ (pow_pos hepos 5) (pow_pos hδ 5)).2
      nlinarith [mul_le_mul_of_nonneg_left hp hK.le]

/-- Enlarging the perturbation factor preserves membership in the perturbation family. -/
lemma perturbation_mono {n : ℕ} {d d' : Point n → Point n → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) {α β : ℝ} (hαβ : α ≤ β)
    (hp : Perturbation d α d') : Perturbation d β d' := by
  refine ⟨hp.1, ?_⟩
  intro x y
  exact ⟨(hp.2 x y).1,
    (hp.2 x y).2.trans (mul_le_mul_of_nonneg_right hαβ (hd x y))⟩

/-- Stability at a larger factor implies stability at every smaller factor. -/
lemma stable_mono {n k : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {α β : ℝ} (hαβ : α ≤ β)
    {O : Partition n} (hO : Stable d k β O) : Stable d k α O := by
  rcases hd with ⟨m, hm⟩
  letI : MetricSpace (Point n) := m
  have hn : ∀ x y, 0 ≤ d x y := by
    intro x y
    rw [← hm x y]
    exact dist_nonneg
  exact ⟨hO.1, fun d' hp => hO.2 d' (perturbation_mono hn hαβ hp)⟩

/-- The same execution and work bound recover all instances with a stronger stability promise. -/
lemma recoversWithin_mono {P : MinSumFPT.Program} {n k budget : ℕ}
    {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {α β : ℝ} (hαβ : α ≤ β)
    (hrec : RecoversWithin P n k d α budget) :
    RecoversWithin P n k d β budget := by
  rcases hrec with ⟨t, ht, hh, hw, hl, hf, ho⟩
  exact ⟨t, ht, hh, hw, hl, hf, fun O hO => ho O (stable_mono hd hαβ hO)⟩

/-- In particular, the factor 3/2 algorithm suffices whenever γ is at least 2. -/
lemma recoversWithin_of_two_le {P : MinSumFPT.Program} {n k budget : ℕ}
    {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {γ : ℝ} (hγ : 2 ≤ γ)
    (hrec : RecoversWithin P n k d (3 / 2) budget) :
    RecoversWithin P n k d γ budget := by
  exact recoversWithin_mono hd (by linarith) hrec

end CalibrationAux
end StableMSR.Recovery

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

/-- Range checking and surjectivity of the output labels supply the feasibility
obligation in the public recovery specification. -/
lemma recoversWithin_of_labels
    (hdecode : ∀ {n k : ℕ} (s : MinSumFPT.State),
      ValidLabels n k s → Feasible Finset.univ k (outputPartition n k s))
    {P : MinSumFPT.Program} {n k budget : ℕ} {d : Point n → Point n → ℝ}
    {γ : ℝ}
    (hexec : ∃ t ≤ budget,
      let s := execute P n k d t
      s.halted = true ∧ s.work ≤ budget ∧ ValidLabels n k s ∧
        ∀ O, Stable d k γ O → outputPartition n k s = O) :
    RecoversWithin P n k d γ budget := by
  obtain ⟨t, ht, hh, hw, hl, ho⟩ := hexec
  exact ⟨t, ht, hh, hw, hl, hdecode _ hl, ho⟩

/-- The real stability theorem reduces to a uniform rational-parameter program,
the numerical parameter envelope, and the exact output-label decoding theorem.
All program, input, execution, and budget quantifiers remain in their original order. -/
theorem deterministic_exact_recovery_of_rational_program
    (henvelope : ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (parameterEnvelope ε : ℝ) ≤ K / ε ^ 5)
    (hdecode : ∀ {n k : ℕ} (s : MinSumFPT.State),
      ValidLabels n k s → Feasible Finset.univ k (outputPartition n k s))
    (hprogram :
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
        ∀ ε₀ : ℚ, 0 < ε₀ → ε₀ < 1 →
          ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
            ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
              1 ≤ k → k ≤ n → IsMetricArray d →
              ∃ t ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)),
                let s := execute P n k d t
                s.halted = true ∧
                  s.work ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)) ∧
                  ValidLabels n k s ∧
                  ∀ O, Stable d k (1 + (ε₀ : ℝ)) O → outputPartition n k s = O) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := by
  obtain ⟨a, b, ha, hb, hprogram⟩ := hprogram
  obtain ⟨K, hK, hE⟩ := henvelope
  obtain ⟨C, hC, hcal⟩ := CalibrationAux.exists_calibration_with_envelope K hK hE
  refine ⟨a, b, ha, hb, C, hC, ?_⟩
  intro γ hγ
  obtain ⟨ε₀, hεpos, hεone, hrange, hbound, hmargin⟩ := hcal γ hγ
  obtain ⟨P, hP, hrun⟩ := hprogram ε₀ hεpos hεone
  refine ⟨ε₀, hεpos, hεone, hrange, hbound, P, hP, ?_⟩
  intro n k d hk hkn hd
  exact CalibrationAux.recoversWithin_mono hd hmargin.le
    (recoversWithin_of_labels hdecode (hrun n k d hk hkn hd))

end StableMSR.Recovery
open StableMSR.Recovery

theorem solution :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := by
  exact deterministic_exact_recovery_of_rational_program
    parameterEnvelope_bound validLabels_feasible rational_recovery_program
