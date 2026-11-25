-- Prove2me | solution 1 for PI.LocMassTypW.WCoreP.model_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:50.872456+00:00
-- url     : https://prove2.me/submissions/e161d862-3ba1-4a45-ae84-0dc360781013

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW PI.LocMassTypW.WCoreP
open Matrix Module
namespace PI.LocMassTypW.WCoreP
theorem _root_.solution {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [AddCommGroup Z] [Module K Z]
    (a : W →ₗ[K] V) (b : V →ₗ[K] W) (s : W →ₗ[K] V) (T : Submodule K W) (ζ : Z →ₗ[K] V)
    (ha : Function.Injective a) (hbs : ∀ w, b (s w) = w)
    (hT : ∀ w, b (a w) ∈ T → b (a w) = 0)
    (hζ : Function.Injective ζ) (hζb : ∀ z, b (ζ z) = 0)
    (hζa : ∀ z w, ζ z = a w → ζ z = 0) :
    Function.Injective (LinearMap.coprod a (LinearMap.coprod (s ∘ₗ T.subtype) ζ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨w, ⟨⟨t, ht⟩, z⟩⟩ h
  simp only [LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h

  have hb := congrArg b h
  rw [map_add, map_add, hbs, hζb, add_zero, map_zero] at hb
  have hbaw : b (a w) ∈ T := by
    rw [eq_neg_of_add_eq_zero_left hb]
    exact T.neg_mem ht
  have h0 := hT w hbaw
  have ht0 : t = 0 := by
    rw [h0, zero_add] at hb
    exact hb
  subst ht0
  rw [map_zero, zero_add] at h
  have hz : ζ z = a (-w) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_right h
  have z0 : z = 0 := hζ (by rw [hζa z (-w) hz, map_zero])
  subst z0
  rw [map_zero, add_zero] at h
  have w0 : w = 0 := ha (by rw [h, map_zero])
  subst w0
  rfl
end PI.LocMassTypW.WCoreP
