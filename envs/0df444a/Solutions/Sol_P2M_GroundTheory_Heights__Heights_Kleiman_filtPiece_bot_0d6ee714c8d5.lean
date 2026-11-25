-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_bot_0d6ee714c8d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:36.072842+00:00
-- url     : https://prove2.me/submissions/7d74125a-9066-45a2-a9bb-40feffe1cf71

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
theorem _root_.solution (hle : ∀ c, M₂.piece c ≤ M₁.piece c) (c : ℤ) :
    filtPiece M₁ M₂ ⊥ c = M₂.piece c := by
  ext z
  rw [mem_filtPiece]
  constructor
  · rintro ⟨h, h0⟩
    exact (quotIota_eq_zero_iff M₁ M₂ ⟨z, h⟩).mp ((Submodule.mem_bot _).mp h0)
  · intro hz
    exact ⟨hle c hz, (Submodule.mem_bot _).mpr ((quotIota_eq_zero_iff M₁ M₂ ⟨z, hle c hz⟩).mpr hz)⟩
end GroundTheory.Heights₂.Heights.Kleiman
