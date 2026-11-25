-- Prove2me | solution 1 for QnRdSkewW.aesm_of_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:34.379976+00:00
-- url     : https://prove2.me/submissions/e84969ec-1d9f-41e1-9cb3-0ccc17647541

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_HasDerivAtShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_IntegrableOfContOn
import Theorems.Thm_QnRdSkewW_cont_of
import Theorems.Thm_QnRdSkewW_ae_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}
namespace QnRdSkewW
theorem _root_.solution (hGc : IsClosed G) (hconc : μ Gᶜ = 0) {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hφ : ContinuousOn φ G) : AEStronglyMeasurable (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x)) μ := by
  have hcl : IsClosed {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G} := hGc.preimage cont_of
  have h1 : ContinuousOn (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x))
      {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G} :=
    hφ.comp cont_of.continuousOn (fun x hx => hx)
  have h2 := h1.aestronglyMeasurable (μ := μ) hcl.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G}) (ae_mem hconc)] at h2
end QnRdSkewW
