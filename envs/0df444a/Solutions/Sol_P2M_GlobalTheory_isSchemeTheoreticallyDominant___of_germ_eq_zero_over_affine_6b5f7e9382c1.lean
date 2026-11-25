-- Prove2me | solution 1 for P2M_GlobalTheory_isSchemeTheoreticallyDominant___of_germ_eq_zero_over_affine_6b5f7e9382c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:12.976371+00:00
-- url     : https://prove2.me/submissions/404058eb-b3f7-4d3e-8684-6719025d8178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchemeTheoreticallyDominantOfGermInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens)
    (h : ∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) :
    IsSchemeTheoreticallyDominant W.ι := by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := X.isBasis_affineOpens.isOpenCover_mem_and_le
    (T.isBasis_affineOpens.isOpenCover.comap p.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U ↦ ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨U, ⟨V, hV⟩⟩, hU, hUV : U ≤ p ⁻¹ᵁ V⟩
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
  intro b hb
  have hb' : W.ι.app U b = 0 := W.ι.ideal_ker_le ⟨U, hU⟩ hb
  refine h U V hU hV hUV b fun x hx hxW ↦ ?_
  have h1 := Scheme.Hom.germ_stalkMap_apply W.ι U ⟨x, hxW⟩ hx b
  rw [hb', map_zero] at h1
  let y : W.toScheme := ⟨x, hxW⟩
  have hiso : IsIso (W.ι.stalkMap y) := inferInstance
  have hinj : Function.Injective (W.ι.stalkMap y) :=
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1
  exact hinj (h1.trans (map_zero _).symm)
end GlobalTheory
