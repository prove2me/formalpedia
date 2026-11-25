-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mulQuotMap_bijective_20064c85c483
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:32.843428+00:00
-- url     : https://prove2.me/submissions/fd2e7dec-26c5-41c8-8ab9-39fae2dbd516

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulQuotEqSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PMulQuotEq

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {F₁ F₂ G₁ G₂ : SubSystem k x Ω} {s : Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₂ : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    Function.Bijective (mulQuotMap h₁ h₃ I) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [LinearMap.mem_ker] at hm
    change Submodule.Quotient.mk (mulSubMap h₁ I y) = 0 at hm
    rw [Submodule.Quotient.mk_eq_zero] at hm
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact (h₃ I y y.2).mp hm
  · intro m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y, hy, hz⟩ := h₂ I z z.2
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    change Submodule.Quotient.mk (mulSubMap h₁ I ⟨y, hy⟩) = Submodule.Quotient.mk z
    rw [Submodule.Quotient.eq]
    change ((mulSubMap h₁ I ⟨y, hy⟩ - z : G₁.sub I) : Ω) ∈ G₂.sub I
    rw [Submodule.coe_sub, ← neg_sub]
    exact (G₂.sub I).neg_mem hz
end GroundTheory.Heights₂.Heights.Kleiman
