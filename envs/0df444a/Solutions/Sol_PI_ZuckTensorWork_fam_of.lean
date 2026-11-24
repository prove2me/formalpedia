-- Prove2me | solution 1 for PI.ZuckTensorWork.fam_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:06:12.792838+00:00
-- url     : https://prove2.me/submissions/0a091506-bbaa-4c3b-8fdc-07b4299d3f4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_DSExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ZuckDualOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
attribute [instance] Fam.nH Fam.iH Fam.cH
namespace PI.ZuckTensorWork
theorem _root_.solution (hE : PI.DSExist) {n : ℕ} (ε : Fin n → Bool) (ν : Fin n → Fin n → ℝ) :
    ∃ F : Fam n, ∀ s, IsHCParam (ν s) → IsDS ε (ν s) (F.σs s) := by
  classical
  have key : ∀ s, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam (ν s) → IsDS ε (ν s) σ := by
    intro s
    by_cases h : IsHCParam (ν s)
    · obtain ⟨H, i1, i2, σ, hσ⟩ := hE n ε (ν s) h
      exact ⟨H, i1, i2, hσ.1, σ, fun _ => hσ⟩
    · exact ⟨ℂ, inferInstance, inferInstance, inferInstance, fun _ => 0, fun h' => absurd h' h⟩
  choose Hs i1 i2 i3 σs hσ using key
  exact ⟨{ Hs := Hs, nH := i1, iH := i2, cH := i3, σs := σs }, hσ⟩
end PI.ZuckTensorWork
