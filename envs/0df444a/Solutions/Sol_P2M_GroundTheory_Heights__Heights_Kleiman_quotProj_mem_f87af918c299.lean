-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mem_f87af918c299
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:03:30.363742+00:00
-- url     : https://prove2.me/submissions/067fa529-695e-49a1-a6dc-2aec42c66a87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mk_85d17fedfeb4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (y : quotLaurent M₁ M₂) : quotProj M₁ M₂ c y ∈ quotPiece M₁ M₂ c := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨_, (quotProj_mk M₁ M₂ c m).symm⟩
end GroundTheory.Heights₂.Heights.Kleiman
