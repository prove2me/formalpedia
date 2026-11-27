-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_absNorm_map_comap_C_24678f6aa93d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:33.955969+00:00
-- url     : https://prove2.me/submissions/feaab08e-4ce0-42bb-9563-70ea16763bcb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
theorem _root_.solution (W : Ideal (MRing (PBlk n))) :
    Ideal.absNorm ((W.comap (C : ℤ →+* MRing (PBlk n))).map (ι : ℤ →+* 𝓞 ℚ)) =
      ReciprocityTheory.ChartRestriction.G.Geo.charOf W := by
  set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing (PBlk n))) with hg
  have hspan : W.comap (C : ℤ →+* MRing (PBlk n)) = Ideal.span {g} :=
    (Ideal.span_singleton_generator _).symm
  rw [hspan, Ideal.map_span, Set.image_singleton, Ideal.absNorm_span_singleton]
  have h1 : (ι : ℤ →+* 𝓞 ℚ) g = algebraMap ℤ (𝓞 ℚ) g :=
    (eq_intCast _ g).trans (eq_intCast _ g).symm
  rw [h1, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
