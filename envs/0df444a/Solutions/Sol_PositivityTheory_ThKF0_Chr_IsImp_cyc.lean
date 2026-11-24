-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.IsImp.cyc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:47.571618+00:00
-- url     : https://prove2.me/submissions/9809442d-7c7c-4352-89b0-09ab7a757927

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_translate_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]
namespace PositivityTheory.ThKF0.Chr
namespace IsImp
theorem _root_.solution {S : V R κ ≃ₗ[R] V R κ} {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T) {φ : (κ → R) → ℂ}
    (hφ : φ ∈ C.sp κ) (h0 : φ ≠ 0) : ∃ w, T (schr ψ w φ) 0 ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 fun e => h0 (hT.inj φ hφ e)
  refine ⟨S.symm (x, 0), ?_⟩
  rw [hT.law _ _ hφ, S.apply_symm_apply, schrodinger_translate_apply]
  simpa using hx
end IsImp
end PositivityTheory.ThKF0.Chr
