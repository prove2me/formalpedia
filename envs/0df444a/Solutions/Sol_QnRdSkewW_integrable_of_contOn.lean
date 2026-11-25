-- Prove2me | solution 1 for QnRdSkewW.integrable_of_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:15.594349+00:00
-- url     : https://prove2.me/submissions/58fcdd70-1f9f-42e8-890f-2fba17c8e0ac

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
theorem _root_.solution (hGc : IsClosed G) (hconc : μ Gᶜ = 0)
    (hfin : ∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hφ : ContinuousOn φ G) {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hK : IsCompact K)
    (hz : ∀ g ∈ G, g ∉ K → φ g = 0) : Integrable (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x)) μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  have hSc : IsCompact {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} := hK.inter_right hGc
  have hcont : ContinuousOn (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x))
      {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} :=
    hφ.comp cont_of.continuousOn (fun x hx => hx.2)
  have hI := hcont.integrableOn_compact (μ := μ) hSc
  have hInd := (integrable_indicator_iff hSc.isClosed.measurableSet).mpr hI
  refine hInd.congr ?_
  filter_upwards [ae_mem hconc] with x hx
  by_cases hxK : (Matrix.of x) ∈ K
  · exact Set.indicator_of_mem (show x ∈ {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} from ⟨hxK, hx⟩) _
  · rw [Set.indicator_of_notMem (fun h => hxK h.1), hz _ hx hxK]
end QnRdSkewW
