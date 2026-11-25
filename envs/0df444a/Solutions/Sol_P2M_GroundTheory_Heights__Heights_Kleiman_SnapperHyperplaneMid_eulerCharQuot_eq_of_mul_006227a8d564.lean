-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_eq_of_mul_006227a8d564
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:50.952191+00:00
-- url     : https://prove2.me/submissions/d42fbd3a-2991-4540-bb30-7a475fc6c765

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
theorem _root_.solution (F₁ F₂ G₁ G₂ : SubSystem k x Ω) (u : Ω)
    (hmap : ∀ I, ∀ y ∈ F₁.sub I, u * y ∈ G₁.sub I)
    (honto : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - u * y ∈ G₂.sub I)
    (hker : ∀ I, ∀ y ∈ F₁.sub I, u * y ∈ G₂.sub I ↔ y ∈ F₂.sub I) :
    eulerCharQuot k G₁ G₂ = eulerCharQuot k F₁ F₂ := by
  have hk : ∀ I, LinearMap.ker (mulQ F₁ G₁ G₂ u hmap I) = SubSystem.quotSub F₁ F₂ I := by
    intro I
    ext y
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact hker I y y.2
  have hs : ∀ I, Function.Surjective (mulQ F₁ G₁ G₂ u hmap I) := by
    intro I z
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, hy, hyz⟩ := honto I z z.2
    refine ⟨⟨y, hy⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    change u * y - (z : Ω) ∈ G₂.sub I
    rw [← neg_sub]
    exact neg_mem hyz
  let φ : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
    fun I => (Submodule.quotEquivOfEq _ _ (hk I).symm).trans (LinearMap.quotKerEquivOfSurjective _ (hs I))
  have hφ : ∀ I J h m, φ J (SubSystem.quotRes F₁ F₂ I J h m) = SubSystem.quotRes G₁ G₂ I J h (φ I m) := by
    intro I J h m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
    simp only [φ, Submodule.mkQ_apply, SubSystem.quotRes, LinearEquiv.trans_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
    rfl
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.hEquivOfEquiv φ hφ i).finrank_eq).symm
end GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
