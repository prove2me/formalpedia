-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_of_5b80ebceba38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:45.549137+00:00
-- url     : https://prove2.me/submissions/d2c4df57-ff60-4e1c-98d2-7552dfcaea81

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
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e)
    (hJ : ∀ (a : ℤ), ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) (y : quotLaurent M₁ M₂) :
    f • y = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    FinGradedSub.mem_laurent]
  intro c
  change (f • (m : LaurentSpace x E)) c ∈ M₂.piece c
  rw [laurent_smul_apply_of_isHomogeneous hf]
  have := hJ (c - e) _ (m.2 (c - e))
  rwa [sub_add_cancel] at this
end GroundTheory.Heights₂.Heights.Kleiman
