-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isProjStable_sup_eea02c2477b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:51.17099+00:00
-- url     : https://prove2.me/submissions/1b35bc0f-738c-4fd5-8579-22508b4e772c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_mem_07ce8f9f59e2

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
theorem _root_.solution {A : Submodule (Poly S N) (quotLaurent M₁ M₂)} (hA : IsProjStable M₁ M₂ A)
    {e : ℤ} (g : M₁.piece e) :
    IsProjStable M₁ M₂ (A ⊔ Submodule.span (Poly S N) {quotIota M₁ M₂ e g}) := by
  intro y hy c
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [map_add]
  exact add_mem (Submodule.mem_sup_left (hA a ha c))
    (Submodule.mem_sup_right (quotProj_smul_iota_mem r g c))
end GroundTheory.Heights₂.Heights.Kleiman
