-- Prove2me | solution 1 for StochLoadBal.Makespan.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T03:58:10.313865+00:00
-- url     : https://prove2.me/submissions/5d7e448e-ae07-4745-9e12-f3c81a137876
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding
import Theorems.Thm_StochLoadBal_Makespan_proposition_1
import Theorems.Thm_StochLoadBal_Makespan_observation_2
import Theorems.Thm_StochLoadBal_Makespan_lemma_6

open MeasureTheory ProbabilityTheory StochLoadBal.Makespan

theorem solution :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (m n : ℕ), 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin m → Fin n → Ω → ℝ),
        (∀ i j, Measurable (X i j)) → (∀ i j ω, 0 ≤ X i j ω) →
        (∀ i j, Integrable (X i j) P) → iIndepFun (fun j ω i => X i j ω) P →
        ∀ M : ℝ, 0 < M →
          ((∃ σ : Fin n → Fin m, expMakespan P X σ ≤ c₀ * M) →
              ∃ y : Fin m → Fin n → ℝ, LPFeasible P (scale M X) 17 y) ∧
          ∀ b : ℝ, 0 ≤ b → ∀ y : Fin m → Fin n → ℝ, LPFeasible P (scale M X) b y →
            (∃ σ : Fin n → Fin m, IsRoundingOutput P (scale M X) b y σ) ∧
            ∀ σ : Fin n → Fin m, IsRoundingOutput P (scale M X) b y σ →
              expMakespan P X σ ≤ (4 * b + 10) * M := by
  obtain ⟨c₀, hc₀, hprop⟩ := StochLoadBal.Makespan.proposition_1
  refine ⟨c₀, hc₀, ?_⟩
  intro m n hm Ω _ P _ X hmeas hnn hint hind M hM
  -- facts about the scaled instance
  have smeas : ∀ i j, Measurable (scale M X i j) := fun i j => (hmeas i j).div_const M
  have snn : ∀ i j ω, 0 ≤ scale M X i j ω := fun i j ω => div_nonneg (hnn i j ω) hM.le
  have sint : ∀ i j, Integrable (scale M X i j) P := fun i j => (hint i j).div_const M
  have sind : iIndepFun (fun j ω i => scale M X i j ω) P := by
    have hg : ∀ j : Fin n, Measurable (fun v : Fin m → ℝ => fun i => v i / M) :=
      fun _ => by fun_prop
    exact hind.comp (fun _ v i => v i / M) hg
  have hscale : ∀ σ : Fin n → Fin m, expMakespan P (scale M X) σ = expMakespan P X σ / M := by
    intro σ
    have hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hpt : ∀ ω, makespan (scale M X) σ ω = makespan X σ ω / M := by
      intro ω
      unfold makespan load scale
      simp_rw [← Finset.sum_div, div_eq_inv_mul]
      rw [Real.mul_iSup_of_nonneg (inv_nonneg.mpr hM.le)]
    unfold expMakespan
    simp_rw [hpt]
    exact integral_div M _
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, hσ⟩
    by_contra hno
    have h1 := hprop m n hm Ω P (scale M X) smeas snn sint sind hno σ
    rw [hscale σ, lt_div_iff₀ hM] at h1
    linarith
  · intro b hb y hy
    refine ⟨(StochLoadBal.Makespan.observation_2 hm P (scale M X) smeas snn sint b hb y hy).2.2.2,
      ?_⟩
    intro σ hσ
    have h6 := StochLoadBal.Makespan.lemma_6 hm P (scale M X) smeas snn sint sind b hb y hy σ hσ
    rw [hscale σ, div_le_iff₀ hM] at h6
    exact h6
