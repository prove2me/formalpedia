-- Prove2me | solution 1 for ProbabilityTheory.lintegral_lintegral_poissonRandomMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:15:08.872439+00:00
-- url     : https://prove2.me/submissions/bd8e9419-24e3-4e58-b402-044cd54a07fa

import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Theorems.Thm_levy_foundations_prmCampbell

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : ProbabilityTheory.IsPoissonPointFamily K X m μ)
    {g : E → ENNReal} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ x, g x ∂(ProbabilityTheory.poissonRandomMeasure K X ω) ∂μ
      = ∫⁻ x, g x ∂m := by
  have hgen : LevyFoundations.IsPoissonPointFamily K X m μ := by
    refine ⟨hd.measurable_count, hd.measurable_point, ?_, ?_, ?_⟩
    · apply (ProbabilityTheory.iIndepFun_iff_iIndep
        (fun i : ℕ ⊕ ℕ × ℕ => LevyFoundations.instPointFamilyIndexMeasurable E i)
        (LevyFoundations.pointFamilyCombined K X) μ).2
      have hind := (ProbabilityTheory.iIndepFun_iff_iIndep
        (fun i : ℕ ⊕ ℕ × ℕ =>
          ProbabilityTheory.instMeasurableSpacePointFamilyIndexType E i)
        (ProbabilityTheory.pointFamilyCombined K X) μ).1 hd.indep
      have heq : (fun i : ℕ ⊕ ℕ × ℕ =>
          MeasurableSpace.comap (ProbabilityTheory.pointFamilyCombined K X i)
            (ProbabilityTheory.instMeasurableSpacePointFamilyIndexType E i)) =
          (fun i => MeasurableSpace.comap (LevyFoundations.pointFamilyCombined K X i)
            (LevyFoundations.instPointFamilyIndexMeasurable E i)) := by
        funext i
        cases i <;> rfl
      rw [heq] at hind
      exact hind
    · intro k
      simpa only [ProbabilityTheory.prmPiece, LevyFoundations.prmPiece] using hd.law_count k
    · intro k n
      convert hd.law_point k n using 1
      unfold ProbabilityTheory.prmPieceLaw LevyFoundations.prmPieceLaw
      simp only [ProbabilityTheory.prmPiece, LevyFoundations.prmPiece]
      split_ifs with h
      · rfl
      · ext s hs
        first | rfl | simp [Measure.smul_apply]
  change ∫⁻ ω, ∫⁻ x, g x ∂(LevyFoundations.poissonRandomMeasure K X ω) ∂μ
    = ∫⁻ x, g x ∂m
  exact levy_foundations_prmCampbell m μ K X hgen hg
