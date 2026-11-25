-- Prove2me | solution 1 for PI.AprimeInfG.lintegral_fin_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:12.108292+00:00
-- url     : https://prove2.me/submissions/26040d73-bb4d-4fc1-b6a8-22ac0d5dbf3f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Set
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace PI.AprimeInfG
theorem _root_.solution {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp [Measure.pi_of_empty]
  | succ n ih =>
    have hmp := measurePreserving_piFinSuccAbove μ 0
    have hg : Measurable fun y : (j : Fin n) → E (Fin.succAbove 0 j) =>
        ∏ j, f (Fin.succAbove 0 j) (y j) :=
      Finset.measurable_prod _ fun j _ => (hf _).comp (measurable_pi_apply j)
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : (i : Fin (n + 1)) → E i,
            (fun z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)) =>
              f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j))
            (MeasurableEquiv.piFinSuccAbove E 0 x) ∂(Measure.pi μ) := by
          congr 1
          funext x
          rw [Fin.prod_univ_succ]
          (try simp only [Fin.succAbove_zero]) <;> rfl
      _ = ∫⁻ z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)),
            f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j)
            ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
          hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
            (fun z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)) =>
              f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j))
      _ = (∫⁻ a, f 0 a ∂μ 0) *
            ∫⁻ y, ∏ j, f (Fin.succAbove 0 j) (y j) ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
          lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
          rw [ih (fun j => f (Fin.succAbove 0 j)) (fun j => hf _), Fin.prod_univ_succ]
          simp [Fin.succAbove_zero]
end PI.AprimeInfG
