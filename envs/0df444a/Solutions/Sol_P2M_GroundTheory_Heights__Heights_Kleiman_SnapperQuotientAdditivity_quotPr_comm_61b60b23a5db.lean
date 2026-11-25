-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_comm_61b60b23a5db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:00.769621+00:00
-- url     : https://prove2.me/submissions/2f41ddef-acb6-4cb7-a693-5833e720b600

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
theorem _root_.solution (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :
    quotPr F₁ F₂ F₃ h32 J (SubSystem.quotRes F₁ F₃ I J h m) =
      SubSystem.quotRes F₁ F₂ I J h (quotPr F₁ F₂ F₃ h32 I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m; rfl
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
