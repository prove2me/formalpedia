-- Prove2me | solution 1 for PI.AprimeInfG.lintegral_fintype_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:42.307075+00:00
-- url     : https://prove2.me/submissions/230d4c89-cbfd-47d5-9d02-22d5a885511b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiDens
import Theorems.Thm_PI_AprimeInfG_lintegral_fin_prod

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
namespace PI.AprimeInfG
theorem _root_.solution {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  have h1 : ∀ y : (i' : Fin (Fintype.card ι)) → E (e i'),
      ∏ i, f i ((MeasurableEquiv.piCongrLeft E e) y i) = ∏ i', f (e i') (y i') := by
    intro y
    exact (Fintype.prod_equiv e (fun i' => f (e i') (y i')) _
      (fun i' => by simp [MeasurableEquiv.piCongrLeft_apply_apply])).symm
  simp_rw [h1]
  rw [lintegral_fin_prod (fun i' => f (e i')) (fun i' => hf (e i'))]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)
end PI.AprimeInfG
