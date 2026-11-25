-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipMap_mem_c41bae6a48c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:05:31.428796+00:00
-- url     : https://prove2.me/submissions/24fe9425-9d67-4a64-a408-449cb90e1b5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
theorem _root_.solution (h : HermitianForm F E W) {La : AddSubgroup W}
    (hsm : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La) (hint : IsIntegralOn h La)
    {x₀ y : W} {c : E} (hx₀ : x₀ ∈ La) (hy : y ∈ La) (hc : c ∈ integralClosure ℤ E)
    {x : W} (hx : x ∈ La) : unipMap h x₀ y c x ∈ La := by
  have smul_mem : ∀ {α : E} {v : W}, α ∈ integralClosure ℤ E → v ∈ La → α • v ∈ La :=
    fun {α} {v} hα hv => hsm ⟨α, hα⟩ v hv
  rw [unipMap_apply]
  refine add_mem (add_mem hx (smul_mem ?_ hx₀)) (smul_mem (hint x₀ hx₀ x hx) hy)
  exact sub_mem (mul_mem (hint x₀ hx₀ x hx) hc) (hint y hy x hx)
end GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
