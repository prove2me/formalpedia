-- Prove2me | solution 1 for PI.FJMB.offD_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:40.669621+00:00
-- url     : https://prove2.me/submissions/11f547bd-7e2b-4211-a400-0717deffe1ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
variable {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
include hι
namespace PI.FJMB
theorem _root_.solution : offD (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) ∪ edge ι = offD ι := by
  ext v
  constructor
  · rintro (⟨i, k, rfl, hik⟩ | (⟨l, rfl⟩ | ⟨j, rfl⟩))
    · exact ⟨i.succ, k.succ, rfl, by simpa using hik⟩
    · exact ⟨0, l.succ, rfl, by simp⟩
    · exact ⟨j.succ, 0, rfl, by simp⟩
  · rintro ⟨i, k, rfl, hik⟩
    cases i using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => simp at hik
      | succ l => exact Or.inr (Or.inl ⟨l, rfl⟩)
    | succ i =>
      cases k using Fin.cases with
      | zero => exact Or.inr (Or.inr ⟨i, rfl⟩)
      | succ l => exact Or.inl ⟨i, l, rfl, by simpa using hik⟩
end PI.FJMB
