-- Prove2me | solution 1 for PositivityTheory.ThKH.Evl.schr_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:34:17.227313+00:00
-- url     : https://prove2.me/submissions/6adf45bd-37b0-47d2-9525-1b46dd91a356

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_addChar
import Theorems.Thm_GlobalTheory_WeilM_nonarch_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Evl
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ : Type} [Fintype κ] {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKH.Evl
theorem _root_.solution (hc : Continuous ψ) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) := by
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have h1 : IsLocallyConstant fun x : κ → k => ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) :=
    hlc.comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const)
  exact ⟨h1.mul (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩
end PositivityTheory.ThKH.Evl
