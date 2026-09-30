-- Prove2me | solution 1 for UnderstandingML.finite_class_uniform_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T13:05:46.923999+00:00
-- url     : https://prove2.me/submissions/fe0d3005-9aed-44c1-9783-98e67b64f6e5

import Theorems.Thm_UnderstandingML_uc_implies_agnostic_pac
import Theorems.Thm_UnderstandingML_hoeffding_inequality

open MeasureTheory UnderstandingML

theorem solution {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (H : Finset Hyp) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hrange : ∀ h ∈ H, ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1) :
    HasUniformConvergenceWith loss (↑H) (fun ε δ ↦ ⌈Real.log (2 * H.card / δ) / (2 * ε ^ 2)⌉₊) ∧
    (∀ A : Learner Z Hyp, IsERMLearner loss (↑H) A →
      IsAgnosticPACWith loss (↑H) A (fun ε δ ↦ ⌈2 * Real.log (2 * H.card / δ) / ε ^ 2⌉₊)) ∧
    (H.Nonempty → AgnosticPACLearnable loss (↑H : Set Hyp)) := by
  -- Part 1: uniform convergence via Hoeffding and a union bound.
  have hUC : HasUniformConvergenceWith loss (↑H)
      (fun ε δ ↦ ⌈Real.log (2 * H.card / δ) / (2 * ε ^ 2)⌉₊) := by
    intro ε δ hε hε1 hδ hδ1 D hD m hm
    have hsub : {S : Fin m → Z | ¬ IsRepresentative loss (↑H) D ε S} ⊆
        ⋃ h ∈ H, {S : Fin m → Z | ε < |(∑ i, loss h (S i)) / m - ∫ z, loss h z ∂D|} := by
      intro S hS
      simp only [IsRepresentative, not_forall, not_le, Set.mem_setOf_eq] at hS
      obtain ⟨h, hh, hlt⟩ := hS
      exact Set.mem_biUnion (x := h) hh hlt
    have hone : ∀ h ∈ H,
        iidLaw D m {S : Fin m → Z | ε < |(∑ i, loss h (S i)) / m - ∫ z, loss h z ∂D|} ≤
          ENNReal.ofReal (2 * Real.exp (-(2 * m * ε ^ 2))) := by
      intro h hh
      have := hoeffding_inequality D (loss h) (hmeas h hh) (a := 0) (b := 1)
        (Filter.Eventually.of_forall fun z ↦ hrange h hh z) m hε
      simpa using this
    calc iidLaw D m {S | ¬ IsRepresentative loss (↑H) D ε S}
        ≤ iidLaw D m (⋃ h ∈ H,
            {S : Fin m → Z | ε < |(∑ i, loss h (S i)) / m - ∫ z, loss h z ∂D|}) :=
          measure_mono hsub
      _ ≤ ∑ h ∈ H, iidLaw D m
            {S : Fin m → Z | ε < |(∑ i, loss h (S i)) / m - ∫ z, loss h z ∂D|} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _h ∈ H, ENNReal.ofReal (2 * Real.exp (-(2 * m * ε ^ 2))) :=
          Finset.sum_le_sum hone
      _ = ENNReal.ofReal (H.card * (2 * Real.exp (-(2 * m * ε ^ 2)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg H.card),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          rcases Nat.eq_zero_or_pos H.card with hc | hc
          · rw [hc]; simp [hδ.le]
          have hcpos : (0 : ℝ) < H.card := by exact_mod_cast hc
          have hm' : Real.log (2 * H.card / δ) / (2 * ε ^ 2) ≤ m :=
            (Nat.le_ceil _).trans (by exact_mod_cast hm)
          have hlog : Real.log (2 * H.card / δ) ≤ 2 * m * ε ^ 2 := by
            rw [div_le_iff₀ (by positivity)] at hm'
            linarith
          have hexp : 2 * H.card / δ ≤ Real.exp (2 * m * ε ^ 2) := by
            rw [← Real.log_le_iff_le_exp (by positivity)]
            exact hlog
          have h2 : Real.exp (-(2 * m * ε ^ 2)) = (Real.exp (2 * m * ε ^ 2))⁻¹ :=
            Real.exp_neg _
          rw [h2]
          have hEpos : 0 < Real.exp (2 * m * ε ^ 2) := Real.exp_pos _
          rw [div_le_iff₀ hδ] at hexp
          rw [show (H.card : ℝ) * (2 * (Real.exp (2 * m * ε ^ 2))⁻¹) =
              2 * H.card / Real.exp (2 * m * ε ^ 2) by field_simp]
          rw [div_le_iff₀ hEpos]
          linarith
  -- Part 2: from Corollary 4.4 with `m^{UC}(ε/2, δ)`.
  have hfun : (fun ε δ : ℝ ↦ ⌈Real.log (2 * H.card / δ) / (2 * (ε / 2) ^ 2)⌉₊) =
      fun ε δ ↦ ⌈2 * Real.log (2 * H.card / δ) / ε ^ 2⌉₊ := by
    funext ε δ
    congr 1
    rcases eq_or_ne ε 0 with rfl | hε
    · simp
    · field_simp
  have hPAC := uc_implies_agnostic_pac loss (↑H) _ hUC
  refine ⟨hUC, fun A hA ↦ ?_, fun hne ↦ ?_⟩
  · have := hPAC.1 A hA
    rw [← hfun]
    exact this
  · -- Part 3: a nonempty finite class admits an ERM learner.
    apply hPAC.2
    refine ⟨fun m S ↦ Classical.choose (H.exists_min_image (empRisk loss S) hne), ?_⟩
    intro m S
    exact Classical.choose_spec (H.exists_min_image (empRisk loss S) hne)
