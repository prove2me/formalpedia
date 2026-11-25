-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_MulQuotEq_proof_72f7cf59d3e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:21.896983+00:00
-- url     : https://prove2.me/submissions/f7338e01-66cb-430e-8c69-0038302f3e9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulQuotEqSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PMulQuotEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mulQuotMap_bijective_20064c85c483

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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace MulQuotEq
theorem _root_.solution : MulQuotEq.Statement.{u, w} := by
  intro k _ Ω _ _ N x F₁ F₂ G₁ G₂ s h₁ h₂ h₃
  let e : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
    fun I => LinearEquiv.ofBijective (mulQuotMap h₁ h₃ I) (mulQuotMap_bijective h₁ h₂ h₃ I)
  have he : ∀ I J h m, e J (SubSystem.quotRes F₁ F₂ I J h m) = SubSystem.quotRes G₁ G₂ I J h (e I m) := by
    intro I J h m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rfl
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.equivH e he i).finrank_eq).symm
end MulQuotEq
end GroundTheory.Heights₂.Heights.Kleiman
