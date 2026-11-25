-- Prove2me | solution 1 for PIW.HCFdeg.irr_repOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:18.875183+00:00
-- url     : https://prove2.me/submissions/f1acb7b9-ac02-4acc-a139-8f36d7cf2029

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
namespace PIW.HCFdeg
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsCRepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) : Irr (repOf ε σ h) := by
  intro S hS hst
  refine hI S hS ?_
  intro g hg v hv
  obtain ⟨x, rfl⟩ : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hg
  exact hst x v hv
end PIW.HCFdeg
