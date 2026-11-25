-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_of_preserves_bd77755a0330
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:08.912874+00:00
-- url     : https://prove2.me/submissions/13d52649-4838-4dcc-9b24-21e9608d563a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHyperbolicPairTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
theorem _root_.solution (h : HermitianForm F E W) [FiniteDimensional E W]
    (f : W →ₗ[E] W) (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) :
    ∃ g : h.unitaryGroup, ∀ z, (g : W ≃ₗ[E] W) z = f z := by
  have inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun z hz => h.nonsingular.1 ?_
    ext y
    rw [← hf, hz, map_zero]
    rfl
  exact ⟨⟨LinearEquiv.ofInjectiveEndo f inj, fun x y => hf x y⟩, fun _ => rfl⟩
end GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
