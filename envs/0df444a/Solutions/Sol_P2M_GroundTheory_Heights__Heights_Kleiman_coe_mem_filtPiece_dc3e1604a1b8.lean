-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coe_mem_filtPiece_dc3e1604a1b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:35.291883+00:00
-- url     : https://prove2.me/submissions/0355e44d-8a3b-4980-bd38-6f0d67cb0619

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded

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
variable {M₁ M₂}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {A : Submodule (Poly S N) (quotLaurent M₁ M₂)} {c : ℤ} (z : M₁.piece c) :
    (z : E) ∈ filtPiece M₁ M₂ A c ↔ quotIota M₁ M₂ c z ∈ A :=
  mem_filtPiece.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨z.2, h⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman
