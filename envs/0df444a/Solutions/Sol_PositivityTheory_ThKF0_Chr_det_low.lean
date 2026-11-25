-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.det_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:36.874962+00:00
-- url     : https://prove2.me/submissions/fd334540-de45-4777-9877-977713793f4c

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_LevScalar2
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsSp_trans


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
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β β₁ ν κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁]
  [Fintype ν] [DecidableEq ν] [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {ι : Matrix β β₁ E} {X : Matrix β ν E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (n : Matrix b a E) (t : GL b E) :
    GeneralLinearGroup.det (low n t) = GeneralLinearGroup.det t :=
  Units.ext ((det_fromBlocks_zero₁₂ 1 n t.1).trans (by rw [det_one, one_mul]; rfl))
end PositivityTheory.ThKF0.Chr
