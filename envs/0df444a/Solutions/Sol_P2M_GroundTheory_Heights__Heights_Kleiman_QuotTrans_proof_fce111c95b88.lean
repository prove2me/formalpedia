-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_proof_fce111c95b88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:19.875171+00:00
-- url     : https://prove2.me/submissions/c2f56c3c-c44c-4506-a8d2-8c727ff48399

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PQuotTrans
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_of_exact_45ae9e3bf583

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
namespace QuotTrans
theorem _root_.solution : QuotTrans.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F₁ F₂ F₃ h32 h21 h23 h12
  unfold SubSystem.quotH at h23 h12 ⊢

  let π : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
    fun I => (SubSystem.quotSub F₁ F₃ I).mapQ (SubSystem.quotSub F₁ F₂ I) LinearMap.id
      (fun y hy => h32 I hy)

  let incl : ∀ I, F₂.sub I →ₗ[S] F₁.sub I := fun I =>
    { toFun := fun y => ⟨y, h21 I y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ι : ∀ I, (F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :=
    fun I => (SubSystem.quotSub F₂ F₃ I).mapQ (SubSystem.quotSub F₁ F₃ I) (incl I) (fun _ hy => hy)
  refine QuotTrans.subsingleton_H_one_of_exact ι π ?_ ?_ ?_ ?_ ?_ ?_ h23 h12
  · intro I J h m
    induction m using Submodule.Quotient.induction_on
    rfl
  · intro I J h m
    induction m using Submodule.Quotient.induction_on
    rfl
  ·
    intro I
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ((Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₃ I)).mp (LinearMap.mem_ker.mp hq))
  · intro I q
    induction q using Submodule.Quotient.induction_on with
    | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩
  ·
    intro I b hb
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      have hy : (y : E) ∈ F₂.sub I := (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mp hb
      exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, rfl⟩
  · intro I J K h h' m
    induction m using Submodule.Quotient.induction_on
    rfl
end QuotTrans
end GroundTheory.Heights₂.Heights.Kleiman
