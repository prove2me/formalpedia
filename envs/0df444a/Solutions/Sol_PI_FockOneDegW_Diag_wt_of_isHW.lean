-- Prove2me | solution 1 for PI.FockOneDegW.Diag.wt_of_isHW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:22.624982+00:00
-- url     : https://prove2.me/submissions/c6bf97d9-fa01-46a8-8b2f-34549bd920a1

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Diag
theorem _root_.solution {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) (h : IsHW act μ v) :
    v ≠ 0 ∧ ∀ a, (act (Eab a a) - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ V)) v = 0 := by
  unfold FockH1Action.IsHW at h
  unfold FockH1Action.hwSub at h
  refine ⟨h.1, fun a => ?_⟩
  have hw := (Submodule.mem_inf.1 h.2).1
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hw
  exact hw a
end PI.FockOneDegW.Diag
