-- Prove2me | solution 1 for PI.UMultOne.GelfSpanWork.spanAlg_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:02.541579+00:00
-- url     : https://prove2.me/submissions/a22e0158-8c0d-41ac-a488-f6c1e485af53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSpanAlgebra_Burnside
import Theorems.Thm_PI_UMultOne_GelfSpanWork_repEnd_apply
import Theorems.Thm_PI_UMultOne_GelfSpanWork_spanAlg_smul
import Theorems.Thm_PI_UMultOne_GelfSpanWork_repEnd_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.GelfSpanWork
open Matrix Module
variable {G : Type} [Group G] {N : ℕ}
namespace PI.UMultOne.GelfSpanWork
theorem _root_.solution (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ) :
    IsSimpleModule (spanAlg ρ) (Fin N → ℂ) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nontrivial (Fin N → ℂ) := inferInstance
  refine { eq_bot_or_eq_top := fun S => ?_ }
  have hT := hI (S.restrictScalars ℂ) (fun g v hv => by
    have := S.smul_mem ⟨repEnd ρ g, repEnd_mem ρ g⟩ hv
    rw [spanAlg_smul] at this
    simpa [repEnd_apply] using this)
  rcases hT with hT | hT
  · left
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ S.restrictScalars ℂ := hv
    rw [hT] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    have : v ∈ S.restrictScalars ℂ := by rw [hT]; trivial
    exact this
end PI.UMultOne.GelfSpanWork
