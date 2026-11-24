-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_mono_1da95a728efe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:35.834977+00:00
-- url     : https://prove2.me/submissions/834b5c74-8166-4c79-984e-f6c21589d516

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
theorem _root_.solution {A B : Submodule (Poly S N) (quotLaurent M₁ M₂)} (hAB : A ≤ B) (c : ℤ) :
    filtPiece M₁ M₂ A c ≤ filtPiece M₁ M₂ B c := by
  intro z hz
  obtain ⟨h, hA⟩ := mem_filtPiece.mp hz
  exact mem_filtPiece.mpr ⟨h, hAB hA⟩
end GroundTheory.Heights₂.Heights.Kleiman
