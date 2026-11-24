-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.tie_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:03.286186+00:00
-- url     : https://prove2.me/submissions/fbb1916d-3e96-45fc-a0be-c64213e0df64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_umat_phi
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_umat_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Set (Formalism.REAL.UJ ε)) :
    {g : Formalism.BasicNotions.UpqT P Q | ∃ a ∈ A, PI.CdHaarScale.umat a = reindex e e (Formalism.BasicNotions.UpqT.mat g)} =
      (phi e h1 h2) ⁻¹' A := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨a, ha, h⟩
    have : a = phi e h1 h2 g := umat_injective (h.trans (umat_phi e h1 h2 g).symm)
    exact this ▸ ha
  · intro hg
    exact ⟨_, hg, umat_phi e h1 h2 g⟩
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
